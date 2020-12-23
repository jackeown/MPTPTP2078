%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:59 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  67 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_76,negated_conjecture,(
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

tff(f_61,axiom,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_36,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_328,plain,(
    ! [A_86,C_87,B_88,D_89] :
      ( r1_tarski(k2_zfmisc_1(A_86,C_87),k2_zfmisc_1(B_88,D_89))
      | ~ r1_tarski(C_87,D_89)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_57,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_38,c_57])).

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

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [A_45,C_46,B_47] :
      ( m1_subset_1(A_45,C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_117,plain,(
    ! [A_51,B_52,A_53] :
      ( m1_subset_1(A_51,B_52)
      | ~ r2_hidden(A_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_147,plain,(
    ! [C_57,B_58,A_59] :
      ( m1_subset_1(C_57,B_58)
      | ~ r1_tarski(k1_zfmisc_1(A_59),B_58)
      | ~ r1_tarski(C_57,A_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_170,plain,(
    ! [C_64,B_65,A_66] :
      ( m1_subset_1(C_64,k1_zfmisc_1(B_65))
      | ~ r1_tarski(C_64,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_20,c_147])).

tff(c_189,plain,(
    ! [B_65] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(B_65))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_7'),B_65) ) ),
    inference(resolution,[status(thm)],[c_69,c_170])).

tff(c_544,plain,(
    ! [B_118,D_119] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(B_118,D_119)))
      | ~ r1_tarski('#skF_7',D_119)
      | ~ r1_tarski('#skF_5',B_118) ) ),
    inference(resolution,[status(thm)],[c_328,c_189])).

tff(c_32,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_552,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_544,c_32])).

tff(c_558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.48  
% 3.09/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2
% 3.09/1.48  
% 3.09/1.48  %Foreground sorts:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Background operators:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Foreground operators:
% 3.09/1.48  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.09/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.09/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.09/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.48  tff('#skF_9', type, '#skF_9': $i).
% 3.09/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.48  
% 3.18/1.49  tff(f_76, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 3.18/1.49  tff(f_44, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 3.18/1.49  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.18/1.49  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.18/1.49  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.18/1.49  tff(f_67, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.18/1.49  tff(c_36, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.49  tff(c_34, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.49  tff(c_328, plain, (![A_86, C_87, B_88, D_89]: (r1_tarski(k2_zfmisc_1(A_86, C_87), k2_zfmisc_1(B_88, D_89)) | ~r1_tarski(C_87, D_89) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.18/1.49  tff(c_38, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.49  tff(c_57, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.18/1.49  tff(c_69, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_57])).
% 3.18/1.49  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.18/1.49  tff(c_8, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.49  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.18/1.49  tff(c_94, plain, (![A_45, C_46, B_47]: (m1_subset_1(A_45, C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.18/1.49  tff(c_117, plain, (![A_51, B_52, A_53]: (m1_subset_1(A_51, B_52) | ~r2_hidden(A_51, A_53) | ~r1_tarski(A_53, B_52))), inference(resolution, [status(thm)], [c_28, c_94])).
% 3.18/1.49  tff(c_147, plain, (![C_57, B_58, A_59]: (m1_subset_1(C_57, B_58) | ~r1_tarski(k1_zfmisc_1(A_59), B_58) | ~r1_tarski(C_57, A_59))), inference(resolution, [status(thm)], [c_8, c_117])).
% 3.18/1.49  tff(c_170, plain, (![C_64, B_65, A_66]: (m1_subset_1(C_64, k1_zfmisc_1(B_65)) | ~r1_tarski(C_64, A_66) | ~r1_tarski(A_66, B_65))), inference(resolution, [status(thm)], [c_20, c_147])).
% 3.18/1.49  tff(c_189, plain, (![B_65]: (m1_subset_1('#skF_9', k1_zfmisc_1(B_65)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_7'), B_65))), inference(resolution, [status(thm)], [c_69, c_170])).
% 3.18/1.49  tff(c_544, plain, (![B_118, D_119]: (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(B_118, D_119))) | ~r1_tarski('#skF_7', D_119) | ~r1_tarski('#skF_5', B_118))), inference(resolution, [status(thm)], [c_328, c_189])).
% 3.18/1.49  tff(c_32, plain, (~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.49  tff(c_552, plain, (~r1_tarski('#skF_7', '#skF_8') | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_544, c_32])).
% 3.18/1.49  tff(c_558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_552])).
% 3.18/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  Inference rules
% 3.18/1.49  ----------------------
% 3.18/1.49  #Ref     : 0
% 3.18/1.49  #Sup     : 128
% 3.18/1.49  #Fact    : 0
% 3.18/1.49  #Define  : 0
% 3.18/1.49  #Split   : 9
% 3.18/1.49  #Chain   : 0
% 3.18/1.49  #Close   : 0
% 3.18/1.49  
% 3.18/1.49  Ordering : KBO
% 3.18/1.49  
% 3.18/1.49  Simplification rules
% 3.18/1.49  ----------------------
% 3.18/1.49  #Subsume      : 7
% 3.18/1.49  #Demod        : 8
% 3.18/1.49  #Tautology    : 10
% 3.18/1.49  #SimpNegUnit  : 0
% 3.18/1.49  #BackRed      : 0
% 3.18/1.49  
% 3.18/1.49  #Partial instantiations: 0
% 3.18/1.49  #Strategies tried      : 1
% 3.18/1.49  
% 3.18/1.49  Timing (in seconds)
% 3.18/1.49  ----------------------
% 3.18/1.49  Preprocessing        : 0.31
% 3.18/1.49  Parsing              : 0.17
% 3.18/1.49  CNF conversion       : 0.03
% 3.18/1.49  Main loop            : 0.42
% 3.18/1.49  Inferencing          : 0.15
% 3.18/1.49  Reduction            : 0.10
% 3.18/1.49  Demodulation         : 0.07
% 3.18/1.49  BG Simplification    : 0.02
% 3.18/1.49  Subsumption          : 0.10
% 3.18/1.49  Abstraction          : 0.02
% 3.18/1.49  MUC search           : 0.00
% 3.18/1.49  Cooper               : 0.00
% 3.18/1.49  Total                : 0.75
% 3.18/1.49  Index Insertion      : 0.00
% 3.18/1.49  Index Deletion       : 0.00
% 3.18/1.49  Index Matching       : 0.00
% 3.18/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
