%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:31 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_setfam_1)).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_15,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_2,c_15])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_setfam_1(A_2,B_3)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_14] : r1_setfam_1(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_20,c_4])).

tff(c_12,plain,(
    ~ r1_setfam_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:32:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.12  %$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 1.59/1.12  
% 1.59/1.12  %Foreground sorts:
% 1.59/1.12  
% 1.59/1.12  
% 1.59/1.12  %Background operators:
% 1.59/1.12  
% 1.59/1.12  
% 1.59/1.12  %Foreground operators:
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.12  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.59/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.59/1.12  
% 1.59/1.12  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.59/1.12  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.59/1.12  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.59/1.12  tff(f_44, negated_conjecture, ~(![A]: r1_setfam_1(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_setfam_1)).
% 1.59/1.12  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.12  tff(c_15, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.59/1.12  tff(c_20, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_2, c_15])).
% 1.59/1.12  tff(c_4, plain, (![A_2, B_3]: (r1_setfam_1(A_2, B_3) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.12  tff(c_24, plain, (![A_14]: (r1_setfam_1(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_20, c_4])).
% 1.59/1.12  tff(c_12, plain, (~r1_setfam_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.12  tff(c_32, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 1.59/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  Inference rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Ref     : 0
% 1.59/1.12  #Sup     : 3
% 1.59/1.12  #Fact    : 0
% 1.59/1.12  #Define  : 0
% 1.59/1.12  #Split   : 0
% 1.59/1.12  #Chain   : 0
% 1.59/1.12  #Close   : 0
% 1.59/1.12  
% 1.59/1.12  Ordering : KBO
% 1.59/1.12  
% 1.59/1.12  Simplification rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Subsume      : 0
% 1.59/1.12  #Demod        : 1
% 1.59/1.12  #Tautology    : 1
% 1.59/1.12  #SimpNegUnit  : 0
% 1.59/1.12  #BackRed      : 1
% 1.59/1.12  
% 1.59/1.12  #Partial instantiations: 0
% 1.59/1.12  #Strategies tried      : 1
% 1.59/1.12  
% 1.59/1.12  Timing (in seconds)
% 1.59/1.12  ----------------------
% 1.59/1.13  Preprocessing        : 0.26
% 1.59/1.13  Parsing              : 0.15
% 1.59/1.13  CNF conversion       : 0.01
% 1.59/1.13  Main loop            : 0.07
% 1.59/1.13  Inferencing          : 0.03
% 1.59/1.13  Reduction            : 0.02
% 1.59/1.13  Demodulation         : 0.01
% 1.59/1.13  BG Simplification    : 0.01
% 1.59/1.13  Subsumption          : 0.01
% 1.59/1.13  Abstraction          : 0.00
% 1.59/1.13  MUC search           : 0.00
% 1.59/1.13  Cooper               : 0.00
% 1.59/1.13  Total                : 0.35
% 1.59/1.13  Index Insertion      : 0.00
% 1.59/1.13  Index Deletion       : 0.00
% 1.59/1.13  Index Matching       : 0.00
% 1.59/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
