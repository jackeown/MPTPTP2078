%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:08 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_29] : k1_subset_1(A_29) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_30] : m1_subset_1(k1_subset_1(A_30),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_27,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_64,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(k1_tarski(B_43),k1_zfmisc_1(A_44))
      | k1_xboole_0 = A_44
      | ~ m1_subset_1(B_43,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_67,plain,
    ( k1_zfmisc_1('#skF_1') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_26])).

tff(c_70,plain,(
    k1_zfmisc_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_67])).

tff(c_22,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_22])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:55:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.15  
% 1.82/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.15  %$ m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1
% 1.82/1.15  
% 1.82/1.15  %Foreground sorts:
% 1.82/1.15  
% 1.82/1.15  
% 1.82/1.15  %Background operators:
% 1.82/1.15  
% 1.82/1.15  
% 1.82/1.15  %Foreground operators:
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.82/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.15  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.82/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.15  
% 1.82/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.82/1.16  tff(f_42, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.82/1.16  tff(f_44, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 1.82/1.16  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.82/1.16  tff(f_57, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.82/1.16  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.82/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.82/1.16  tff(c_18, plain, (![A_29]: (k1_subset_1(A_29)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.82/1.16  tff(c_20, plain, (![A_30]: (m1_subset_1(k1_subset_1(A_30), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.82/1.16  tff(c_27, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 1.82/1.16  tff(c_64, plain, (![B_43, A_44]: (m1_subset_1(k1_tarski(B_43), k1_zfmisc_1(A_44)) | k1_xboole_0=A_44 | ~m1_subset_1(B_43, A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.82/1.16  tff(c_26, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.16  tff(c_67, plain, (k1_zfmisc_1('#skF_1')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_26])).
% 1.82/1.16  tff(c_70, plain, (k1_zfmisc_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_27, c_67])).
% 1.82/1.16  tff(c_22, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.82/1.16  tff(c_79, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_22])).
% 1.82/1.16  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_79])).
% 1.82/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  Inference rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Ref     : 0
% 1.82/1.16  #Sup     : 14
% 1.82/1.16  #Fact    : 0
% 1.82/1.16  #Define  : 0
% 1.82/1.16  #Split   : 0
% 1.82/1.16  #Chain   : 0
% 1.82/1.16  #Close   : 0
% 1.82/1.16  
% 1.82/1.16  Ordering : KBO
% 1.82/1.16  
% 1.82/1.16  Simplification rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Subsume      : 0
% 1.82/1.16  #Demod        : 4
% 1.82/1.16  #Tautology    : 9
% 1.82/1.16  #SimpNegUnit  : 0
% 1.82/1.16  #BackRed      : 1
% 1.82/1.16  
% 1.82/1.16  #Partial instantiations: 0
% 1.82/1.16  #Strategies tried      : 1
% 1.82/1.16  
% 1.82/1.16  Timing (in seconds)
% 1.82/1.16  ----------------------
% 1.82/1.16  Preprocessing        : 0.30
% 1.82/1.16  Parsing              : 0.16
% 1.82/1.16  CNF conversion       : 0.02
% 1.82/1.16  Main loop            : 0.09
% 1.82/1.16  Inferencing          : 0.04
% 1.82/1.17  Reduction            : 0.03
% 1.82/1.17  Demodulation         : 0.02
% 1.82/1.17  BG Simplification    : 0.01
% 1.82/1.17  Subsumption          : 0.01
% 1.82/1.17  Abstraction          : 0.01
% 1.82/1.17  MUC search           : 0.00
% 1.82/1.17  Cooper               : 0.00
% 1.82/1.17  Total                : 0.42
% 1.82/1.17  Index Insertion      : 0.00
% 1.82/1.17  Index Deletion       : 0.00
% 1.82/1.17  Index Matching       : 0.00
% 1.82/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
