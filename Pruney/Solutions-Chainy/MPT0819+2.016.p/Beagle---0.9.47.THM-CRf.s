%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:00 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  67 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_38,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_10,C_12,B_11,D_13] :
      ( r1_tarski(k2_zfmisc_1(A_10,C_12),k2_zfmisc_1(B_11,D_13))
      | ~ r1_tarski(C_12,D_13)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_65,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_zfmisc_1(A_14),k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_96,plain,(
    ! [A_46,C_47,B_48] :
      ( m1_subset_1(A_46,C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128,plain,(
    ! [A_53,B_54,A_55] :
      ( m1_subset_1(A_53,B_54)
      | ~ r2_hidden(A_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_30,c_96])).

tff(c_160,plain,(
    ! [C_64,B_65,A_66] :
      ( m1_subset_1(C_64,B_65)
      | ~ r1_tarski(k1_zfmisc_1(A_66),B_65)
      | ~ r1_tarski(C_64,A_66) ) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_184,plain,(
    ! [C_72,B_73,A_74] :
      ( m1_subset_1(C_72,k1_zfmisc_1(B_73))
      | ~ r1_tarski(C_72,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(resolution,[status(thm)],[c_20,c_160])).

tff(c_249,plain,(
    ! [B_85] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(B_85))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_7'),B_85) ) ),
    inference(resolution,[status(thm)],[c_65,c_184])).

tff(c_847,plain,(
    ! [B_159,D_160] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(B_159,D_160)))
      | ~ r1_tarski('#skF_7',D_160)
      | ~ r1_tarski('#skF_5',B_159) ) ),
    inference(resolution,[status(thm)],[c_18,c_249])).

tff(c_34,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_855,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_847,c_34])).

tff(c_861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:54:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.50  
% 3.30/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2
% 3.30/1.51  
% 3.30/1.51  %Foreground sorts:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Background operators:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Foreground operators:
% 3.30/1.51  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.30/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.30/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.30/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.30/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.30/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.30/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.30/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.51  
% 3.30/1.52  tff(f_79, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 3.30/1.52  tff(f_44, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 3.30/1.52  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.30/1.52  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.30/1.52  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.30/1.52  tff(f_70, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.30/1.52  tff(c_38, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.30/1.52  tff(c_36, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.30/1.52  tff(c_18, plain, (![A_10, C_12, B_11, D_13]: (r1_tarski(k2_zfmisc_1(A_10, C_12), k2_zfmisc_1(B_11, D_13)) | ~r1_tarski(C_12, D_13) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.30/1.52  tff(c_40, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.30/1.52  tff(c_54, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.52  tff(c_65, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_54])).
% 3.30/1.52  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.30/1.52  tff(c_8, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.30/1.52  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.52  tff(c_96, plain, (![A_46, C_47, B_48]: (m1_subset_1(A_46, C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.30/1.52  tff(c_128, plain, (![A_53, B_54, A_55]: (m1_subset_1(A_53, B_54) | ~r2_hidden(A_53, A_55) | ~r1_tarski(A_55, B_54))), inference(resolution, [status(thm)], [c_30, c_96])).
% 3.30/1.52  tff(c_160, plain, (![C_64, B_65, A_66]: (m1_subset_1(C_64, B_65) | ~r1_tarski(k1_zfmisc_1(A_66), B_65) | ~r1_tarski(C_64, A_66))), inference(resolution, [status(thm)], [c_8, c_128])).
% 3.30/1.52  tff(c_184, plain, (![C_72, B_73, A_74]: (m1_subset_1(C_72, k1_zfmisc_1(B_73)) | ~r1_tarski(C_72, A_74) | ~r1_tarski(A_74, B_73))), inference(resolution, [status(thm)], [c_20, c_160])).
% 3.30/1.52  tff(c_249, plain, (![B_85]: (m1_subset_1('#skF_9', k1_zfmisc_1(B_85)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_7'), B_85))), inference(resolution, [status(thm)], [c_65, c_184])).
% 3.30/1.52  tff(c_847, plain, (![B_159, D_160]: (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(B_159, D_160))) | ~r1_tarski('#skF_7', D_160) | ~r1_tarski('#skF_5', B_159))), inference(resolution, [status(thm)], [c_18, c_249])).
% 3.30/1.52  tff(c_34, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.30/1.52  tff(c_855, plain, (~r1_tarski('#skF_7', '#skF_8') | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_847, c_34])).
% 3.30/1.52  tff(c_861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_855])).
% 3.30/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.52  
% 3.30/1.52  Inference rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Ref     : 0
% 3.30/1.52  #Sup     : 207
% 3.30/1.52  #Fact    : 0
% 3.30/1.52  #Define  : 0
% 3.30/1.52  #Split   : 13
% 3.30/1.52  #Chain   : 0
% 3.30/1.52  #Close   : 0
% 3.30/1.52  
% 3.30/1.52  Ordering : KBO
% 3.30/1.52  
% 3.30/1.52  Simplification rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Subsume      : 12
% 3.30/1.52  #Demod        : 8
% 3.30/1.52  #Tautology    : 12
% 3.30/1.52  #SimpNegUnit  : 0
% 3.30/1.52  #BackRed      : 0
% 3.30/1.52  
% 3.30/1.52  #Partial instantiations: 0
% 3.30/1.52  #Strategies tried      : 1
% 3.30/1.52  
% 3.30/1.52  Timing (in seconds)
% 3.30/1.52  ----------------------
% 3.30/1.52  Preprocessing        : 0.29
% 3.30/1.52  Parsing              : 0.16
% 3.30/1.52  CNF conversion       : 0.02
% 3.30/1.52  Main loop            : 0.46
% 3.30/1.52  Inferencing          : 0.17
% 3.30/1.52  Reduction            : 0.11
% 3.30/1.52  Demodulation         : 0.07
% 3.30/1.52  BG Simplification    : 0.02
% 3.30/1.52  Subsumption          : 0.12
% 3.30/1.52  Abstraction          : 0.02
% 3.30/1.52  MUC search           : 0.00
% 3.30/1.52  Cooper               : 0.00
% 3.30/1.52  Total                : 0.78
% 3.30/1.52  Index Insertion      : 0.00
% 3.30/1.52  Index Deletion       : 0.00
% 3.30/1.52  Index Matching       : 0.00
% 3.30/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
