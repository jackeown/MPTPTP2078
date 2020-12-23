%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:23 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  24 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_finset_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k6_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_finset_1)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_finset_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_finset_1)).

tff(c_10,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : m1_subset_1(k6_subset_1(A_1,B_2),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_1,B_2] : m1_subset_1(k4_xboole_0(A_1,B_2),k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2])).

tff(c_23,plain,(
    ! [B_12,A_13] :
      ( v1_finset_1(B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_13))
      | ~ v1_finset_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( v1_finset_1(k4_xboole_0(A_14,B_15))
      | ~ v1_finset_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_8,plain,(
    ~ v1_finset_1(k6_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11,plain,(
    ~ v1_finset_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_31,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_11])).

tff(c_35,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.08  %$ m1_subset_1 > v1_finset_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.62/1.08  
% 1.62/1.08  %Foreground sorts:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Background operators:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Foreground operators:
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.08  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.62/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.08  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.62/1.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.62/1.08  
% 1.62/1.09  tff(f_41, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k6_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_finset_1)).
% 1.62/1.09  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.62/1.09  tff(f_27, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 1.62/1.09  tff(f_36, axiom, (![A]: (v1_finset_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_finset_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_finset_1)).
% 1.62/1.09  tff(c_10, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.09  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.09  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k6_subset_1(A_1, B_2), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.09  tff(c_12, plain, (![A_1, B_2]: (m1_subset_1(k4_xboole_0(A_1, B_2), k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2])).
% 1.62/1.09  tff(c_23, plain, (![B_12, A_13]: (v1_finset_1(B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_13)) | ~v1_finset_1(A_13))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.09  tff(c_28, plain, (![A_14, B_15]: (v1_finset_1(k4_xboole_0(A_14, B_15)) | ~v1_finset_1(A_14))), inference(resolution, [status(thm)], [c_12, c_23])).
% 1.62/1.09  tff(c_8, plain, (~v1_finset_1(k6_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.09  tff(c_11, plain, (~v1_finset_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.62/1.09  tff(c_31, plain, (~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_11])).
% 1.62/1.09  tff(c_35, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_31])).
% 1.62/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  Inference rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Ref     : 0
% 1.62/1.09  #Sup     : 4
% 1.62/1.09  #Fact    : 0
% 1.62/1.09  #Define  : 0
% 1.62/1.09  #Split   : 0
% 1.62/1.09  #Chain   : 0
% 1.62/1.09  #Close   : 0
% 1.62/1.09  
% 1.62/1.09  Ordering : KBO
% 1.62/1.09  
% 1.62/1.09  Simplification rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Subsume      : 0
% 1.62/1.09  #Demod        : 3
% 1.62/1.09  #Tautology    : 2
% 1.62/1.09  #SimpNegUnit  : 0
% 1.62/1.09  #BackRed      : 0
% 1.62/1.09  
% 1.62/1.09  #Partial instantiations: 0
% 1.62/1.09  #Strategies tried      : 1
% 1.62/1.09  
% 1.62/1.09  Timing (in seconds)
% 1.62/1.09  ----------------------
% 1.62/1.09  Preprocessing        : 0.26
% 1.62/1.09  Parsing              : 0.14
% 1.62/1.09  CNF conversion       : 0.01
% 1.62/1.09  Main loop            : 0.06
% 1.62/1.09  Inferencing          : 0.03
% 1.62/1.09  Reduction            : 0.02
% 1.62/1.09  Demodulation         : 0.01
% 1.62/1.09  BG Simplification    : 0.01
% 1.62/1.09  Subsumption          : 0.00
% 1.62/1.09  Abstraction          : 0.01
% 1.62/1.09  MUC search           : 0.00
% 1.62/1.09  Cooper               : 0.00
% 1.62/1.10  Total                : 0.35
% 1.62/1.10  Index Insertion      : 0.00
% 1.62/1.10  Index Deletion       : 0.00
% 1.62/1.10  Index Matching       : 0.00
% 1.62/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
