%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:09 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [B_49,A_50] :
      ( m1_subset_1(k1_tarski(B_49),k1_zfmisc_1(A_50))
      | k1_xboole_0 = A_50
      | ~ m1_subset_1(B_49,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_66,plain,
    ( k1_zfmisc_1('#skF_1') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_61,c_26])).

tff(c_70,plain,(
    k1_zfmisc_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_18,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_18])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:53:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 1.70/1.12  
% 1.70/1.12  %Foreground sorts:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Background operators:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Foreground operators:
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.70/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.12  
% 1.70/1.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.70/1.13  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.70/1.13  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.70/1.13  tff(f_61, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.70/1.13  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.70/1.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.70/1.13  tff(c_20, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.13  tff(c_61, plain, (![B_49, A_50]: (m1_subset_1(k1_tarski(B_49), k1_zfmisc_1(A_50)) | k1_xboole_0=A_50 | ~m1_subset_1(B_49, A_50))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.70/1.13  tff(c_26, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.70/1.13  tff(c_66, plain, (k1_zfmisc_1('#skF_1')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_61, c_26])).
% 1.70/1.13  tff(c_70, plain, (k1_zfmisc_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66])).
% 1.70/1.13  tff(c_18, plain, (![A_29]: (~v1_xboole_0(k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.70/1.13  tff(c_81, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_18])).
% 1.70/1.13  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_81])).
% 1.70/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.13  
% 1.70/1.13  Inference rules
% 1.70/1.13  ----------------------
% 1.70/1.13  #Ref     : 0
% 1.70/1.13  #Sup     : 15
% 1.70/1.13  #Fact    : 0
% 1.70/1.13  #Define  : 0
% 1.70/1.13  #Split   : 0
% 1.70/1.13  #Chain   : 0
% 1.70/1.13  #Close   : 0
% 1.70/1.13  
% 1.70/1.13  Ordering : KBO
% 1.70/1.13  
% 1.70/1.13  Simplification rules
% 1.70/1.13  ----------------------
% 1.70/1.13  #Subsume      : 0
% 1.70/1.13  #Demod        : 3
% 1.70/1.13  #Tautology    : 7
% 1.70/1.13  #SimpNegUnit  : 0
% 1.70/1.13  #BackRed      : 1
% 1.70/1.13  
% 1.70/1.13  #Partial instantiations: 0
% 1.70/1.13  #Strategies tried      : 1
% 1.70/1.13  
% 1.70/1.13  Timing (in seconds)
% 1.70/1.13  ----------------------
% 1.70/1.13  Preprocessing        : 0.29
% 1.70/1.13  Parsing              : 0.16
% 1.70/1.13  CNF conversion       : 0.02
% 1.70/1.14  Main loop            : 0.09
% 1.70/1.14  Inferencing          : 0.04
% 1.70/1.14  Reduction            : 0.03
% 1.70/1.14  Demodulation         : 0.02
% 1.70/1.14  BG Simplification    : 0.01
% 1.70/1.14  Subsumption          : 0.01
% 1.70/1.14  Abstraction          : 0.01
% 1.70/1.14  MUC search           : 0.00
% 1.70/1.14  Cooper               : 0.00
% 1.70/1.14  Total                : 0.41
% 1.70/1.14  Index Insertion      : 0.00
% 1.70/1.14  Index Deletion       : 0.00
% 1.70/1.14  Index Matching       : 0.00
% 1.70/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
