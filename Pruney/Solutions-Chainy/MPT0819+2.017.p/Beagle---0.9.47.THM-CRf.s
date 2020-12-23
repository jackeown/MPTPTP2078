%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:00 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  70 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r1_tarski(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4))
      | ~ r1_tarski(C_3,D_4)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_zfmisc_1(A_5),k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [A_24,C_25,B_26] :
      ( m1_subset_1(A_24,C_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_28,B_29,A_30] :
      ( m1_subset_1(A_28,B_29)
      | ~ r2_hidden(A_28,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_52,plain,(
    ! [A_31,B_32,B_33] :
      ( m1_subset_1(A_31,B_32)
      | ~ r1_tarski(B_33,B_32)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_31,B_33) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_54,plain,(
    ! [A_31,B_6,A_5] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_6))
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ m1_subset_1(A_31,k1_zfmisc_1(A_5))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_74,plain,(
    ! [A_38,B_39,A_40] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ m1_subset_1(A_38,k1_zfmisc_1(A_40))
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_54])).

tff(c_81,plain,(
    ! [B_41] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_41))
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),B_41) ) ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_219,plain,(
    ! [B_66,D_67] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_66,D_67)))
      | ~ r1_tarski('#skF_3',D_67)
      | ~ r1_tarski('#skF_1',B_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_81])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_229,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_219,c_16])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.65  
% 2.70/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.66  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.70/1.66  
% 2.70/1.66  %Foreground sorts:
% 2.70/1.66  
% 2.70/1.66  
% 2.70/1.66  %Background operators:
% 2.70/1.66  
% 2.70/1.66  
% 2.70/1.66  %Foreground operators:
% 2.70/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.66  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.66  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.66  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.66  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.66  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.66  
% 2.70/1.67  tff(f_63, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 2.70/1.67  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.70/1.67  tff(f_38, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.70/1.67  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.70/1.67  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.70/1.67  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.70/1.67  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.70/1.67  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.67  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.67  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (r1_tarski(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)) | ~r1_tarski(C_3, D_4) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.67  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.67  tff(c_6, plain, (![A_7]: (~v1_xboole_0(k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.70/1.67  tff(c_4, plain, (![A_5, B_6]: (r1_tarski(k1_zfmisc_1(A_5), k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.67  tff(c_8, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.70/1.67  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.67  tff(c_40, plain, (![A_24, C_25, B_26]: (m1_subset_1(A_24, C_25) | ~m1_subset_1(B_26, k1_zfmisc_1(C_25)) | ~r2_hidden(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.70/1.67  tff(c_48, plain, (![A_28, B_29, A_30]: (m1_subset_1(A_28, B_29) | ~r2_hidden(A_28, A_30) | ~r1_tarski(A_30, B_29))), inference(resolution, [status(thm)], [c_12, c_40])).
% 2.70/1.67  tff(c_52, plain, (![A_31, B_32, B_33]: (m1_subset_1(A_31, B_32) | ~r1_tarski(B_33, B_32) | v1_xboole_0(B_33) | ~m1_subset_1(A_31, B_33))), inference(resolution, [status(thm)], [c_8, c_48])).
% 2.70/1.67  tff(c_54, plain, (![A_31, B_6, A_5]: (m1_subset_1(A_31, k1_zfmisc_1(B_6)) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~m1_subset_1(A_31, k1_zfmisc_1(A_5)) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_4, c_52])).
% 2.70/1.67  tff(c_74, plain, (![A_38, B_39, A_40]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~m1_subset_1(A_38, k1_zfmisc_1(A_40)) | ~r1_tarski(A_40, B_39))), inference(negUnitSimplification, [status(thm)], [c_6, c_54])).
% 2.70/1.67  tff(c_81, plain, (![B_41]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_41)) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), B_41))), inference(resolution, [status(thm)], [c_22, c_74])).
% 2.70/1.67  tff(c_219, plain, (![B_66, D_67]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_66, D_67))) | ~r1_tarski('#skF_3', D_67) | ~r1_tarski('#skF_1', B_66))), inference(resolution, [status(thm)], [c_2, c_81])).
% 2.70/1.67  tff(c_16, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.70/1.67  tff(c_229, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_219, c_16])).
% 2.70/1.67  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_229])).
% 2.70/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.67  
% 2.70/1.67  Inference rules
% 2.70/1.67  ----------------------
% 2.70/1.67  #Ref     : 0
% 2.70/1.67  #Sup     : 51
% 2.70/1.67  #Fact    : 0
% 2.70/1.67  #Define  : 0
% 2.70/1.67  #Split   : 7
% 2.70/1.67  #Chain   : 0
% 2.70/1.67  #Close   : 0
% 2.70/1.67  
% 2.70/1.67  Ordering : KBO
% 2.70/1.67  
% 2.70/1.67  Simplification rules
% 2.70/1.68  ----------------------
% 2.70/1.68  #Subsume      : 0
% 2.70/1.68  #Demod        : 3
% 2.70/1.68  #Tautology    : 2
% 2.70/1.68  #SimpNegUnit  : 1
% 2.70/1.68  #BackRed      : 0
% 2.70/1.68  
% 2.70/1.68  #Partial instantiations: 0
% 2.70/1.68  #Strategies tried      : 1
% 2.70/1.68  
% 2.70/1.68  Timing (in seconds)
% 2.70/1.68  ----------------------
% 2.78/1.68  Preprocessing        : 0.42
% 2.78/1.68  Parsing              : 0.23
% 2.78/1.68  CNF conversion       : 0.03
% 2.78/1.68  Main loop            : 0.39
% 2.78/1.68  Inferencing          : 0.16
% 2.78/1.68  Reduction            : 0.10
% 2.78/1.68  Demodulation         : 0.06
% 2.78/1.68  BG Simplification    : 0.02
% 2.78/1.68  Subsumption          : 0.09
% 2.78/1.68  Abstraction          : 0.01
% 2.78/1.68  MUC search           : 0.00
% 2.78/1.68  Cooper               : 0.00
% 2.78/1.68  Total                : 0.86
% 2.78/1.68  Index Insertion      : 0.00
% 2.78/1.68  Index Deletion       : 0.00
% 2.78/1.68  Index Matching       : 0.00
% 2.78/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
