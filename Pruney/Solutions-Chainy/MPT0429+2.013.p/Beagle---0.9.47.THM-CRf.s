%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:07 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [C_34,A_30] :
      ( r2_hidden(C_34,k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(k2_tarski(A_67,B_68),C_69)
      | ~ r2_hidden(B_68,C_69)
      | ~ r2_hidden(A_67,C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    ! [A_72,C_73] :
      ( r1_tarski(k1_tarski(A_72),C_73)
      | ~ r2_hidden(A_72,C_73)
      | ~ r2_hidden(A_72,C_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_51,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(A_42,k1_zfmisc_1(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_51,c_40])).

tff(c_124,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_116,c_55])).

tff(c_127,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.24  
% 1.98/1.25  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.98/1.25  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.98/1.25  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.98/1.25  tff(f_54, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.98/1.25  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.98/1.25  tff(f_61, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.98/1.25  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.25  tff(c_20, plain, (![C_34, A_30]: (r2_hidden(C_34, k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.98/1.25  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.25  tff(c_103, plain, (![A_67, B_68, C_69]: (r1_tarski(k2_tarski(A_67, B_68), C_69) | ~r2_hidden(B_68, C_69) | ~r2_hidden(A_67, C_69))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.25  tff(c_116, plain, (![A_72, C_73]: (r1_tarski(k1_tarski(A_72), C_73) | ~r2_hidden(A_72, C_73) | ~r2_hidden(A_72, C_73))), inference(superposition, [status(thm), theory('equality')], [c_4, c_103])).
% 1.98/1.25  tff(c_51, plain, (![A_42, B_43]: (m1_subset_1(A_42, k1_zfmisc_1(B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.25  tff(c_40, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.98/1.25  tff(c_55, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_51, c_40])).
% 1.98/1.25  tff(c_124, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_116, c_55])).
% 1.98/1.25  tff(c_127, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_20, c_124])).
% 1.98/1.25  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 1.98/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  Inference rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Ref     : 0
% 1.98/1.25  #Sup     : 19
% 1.98/1.25  #Fact    : 0
% 1.98/1.25  #Define  : 0
% 1.98/1.25  #Split   : 0
% 1.98/1.25  #Chain   : 0
% 1.98/1.25  #Close   : 0
% 1.98/1.25  
% 1.98/1.25  Ordering : KBO
% 1.98/1.25  
% 1.98/1.25  Simplification rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Subsume      : 1
% 1.98/1.25  #Demod        : 1
% 1.98/1.25  #Tautology    : 13
% 1.98/1.25  #SimpNegUnit  : 0
% 1.98/1.25  #BackRed      : 0
% 1.98/1.25  
% 1.98/1.25  #Partial instantiations: 0
% 1.98/1.25  #Strategies tried      : 1
% 1.98/1.25  
% 1.98/1.25  Timing (in seconds)
% 1.98/1.25  ----------------------
% 1.98/1.25  Preprocessing        : 0.33
% 1.98/1.25  Parsing              : 0.17
% 1.98/1.25  CNF conversion       : 0.02
% 1.98/1.25  Main loop            : 0.11
% 1.98/1.25  Inferencing          : 0.04
% 1.98/1.25  Reduction            : 0.04
% 1.98/1.25  Demodulation         : 0.03
% 1.98/1.25  BG Simplification    : 0.01
% 1.98/1.25  Subsumption          : 0.02
% 1.98/1.25  Abstraction          : 0.01
% 1.98/1.25  MUC search           : 0.00
% 1.98/1.25  Cooper               : 0.00
% 1.98/1.25  Total                : 0.47
% 1.98/1.25  Index Insertion      : 0.00
% 1.98/1.25  Index Deletion       : 0.00
% 1.98/1.25  Index Matching       : 0.00
% 1.98/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
