%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:10 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] : k1_zfmisc_1(k3_xboole_0(A,B)) = k3_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_14,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_34,B_35] : k3_xboole_0(k1_zfmisc_1(A_34),k1_zfmisc_1(B_35)) = k1_zfmisc_1(k3_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_36,B_37] : r1_tarski(k1_zfmisc_1(k3_xboole_0(A_36,B_37)),k1_zfmisc_1(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_2])).

tff(c_113,plain,(
    ! [A_3] : r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_117,plain,(
    ! [A_3] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_113])).

tff(c_52,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_22])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.47  
% 2.28/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.47  %$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 2.28/1.47  
% 2.28/1.47  %Foreground sorts:
% 2.28/1.47  
% 2.28/1.47  
% 2.28/1.47  %Background operators:
% 2.28/1.47  
% 2.28/1.47  
% 2.28/1.47  %Foreground operators:
% 2.28/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.47  
% 2.29/1.49  tff(f_38, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.29/1.49  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.29/1.49  tff(f_40, axiom, (![A, B]: (k1_zfmisc_1(k3_xboole_0(A, B)) = k3_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 2.29/1.49  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.29/1.49  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.29/1.49  tff(f_47, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.29/1.49  tff(c_14, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.29/1.49  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.49  tff(c_88, plain, (![A_34, B_35]: (k3_xboole_0(k1_zfmisc_1(A_34), k1_zfmisc_1(B_35))=k1_zfmisc_1(k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.29/1.49  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.29/1.49  tff(c_107, plain, (![A_36, B_37]: (r1_tarski(k1_zfmisc_1(k3_xboole_0(A_36, B_37)), k1_zfmisc_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_2])).
% 2.29/1.49  tff(c_113, plain, (![A_3]: (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_zfmisc_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_107])).
% 2.29/1.49  tff(c_117, plain, (![A_3]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_113])).
% 2.29/1.49  tff(c_52, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.49  tff(c_22, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.29/1.49  tff(c_63, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_22])).
% 2.29/1.49  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_63])).
% 2.29/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.49  
% 2.29/1.49  Inference rules
% 2.29/1.49  ----------------------
% 2.29/1.49  #Ref     : 0
% 2.29/1.49  #Sup     : 26
% 2.29/1.49  #Fact    : 0
% 2.29/1.49  #Define  : 0
% 2.29/1.49  #Split   : 0
% 2.29/1.49  #Chain   : 0
% 2.29/1.49  #Close   : 0
% 2.29/1.49  
% 2.29/1.49  Ordering : KBO
% 2.29/1.49  
% 2.29/1.49  Simplification rules
% 2.29/1.49  ----------------------
% 2.29/1.49  #Subsume      : 0
% 2.29/1.49  #Demod        : 4
% 2.29/1.49  #Tautology    : 16
% 2.29/1.49  #SimpNegUnit  : 0
% 2.29/1.49  #BackRed      : 1
% 2.29/1.49  
% 2.29/1.49  #Partial instantiations: 0
% 2.29/1.49  #Strategies tried      : 1
% 2.29/1.49  
% 2.29/1.49  Timing (in seconds)
% 2.29/1.49  ----------------------
% 2.29/1.49  Preprocessing        : 0.45
% 2.29/1.49  Parsing              : 0.23
% 2.29/1.49  CNF conversion       : 0.03
% 2.29/1.49  Main loop            : 0.21
% 2.29/1.49  Inferencing          : 0.09
% 2.29/1.49  Reduction            : 0.06
% 2.29/1.49  Demodulation         : 0.05
% 2.29/1.49  BG Simplification    : 0.02
% 2.29/1.49  Subsumption          : 0.03
% 2.29/1.49  Abstraction          : 0.01
% 2.29/1.49  MUC search           : 0.00
% 2.29/1.49  Cooper               : 0.00
% 2.29/1.49  Total                : 0.71
% 2.29/1.49  Index Insertion      : 0.00
% 2.29/1.49  Index Deletion       : 0.00
% 2.29/1.49  Index Matching       : 0.00
% 2.29/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
