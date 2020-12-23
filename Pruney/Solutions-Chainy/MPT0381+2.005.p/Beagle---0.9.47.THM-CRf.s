%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:02 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(c_26,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(k1_tarski(A_49),B_50) = k1_tarski(A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_82,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_100,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_17,B_18] : m1_subset_1(k6_subset_1(A_17,B_18),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27,plain,(
    ! [A_17,B_18] : m1_subset_1(k4_xboole_0(A_17,B_18),k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_118,plain,(
    ! [A_38,B_39] : m1_subset_1(k3_xboole_0(A_38,B_39),k1_zfmisc_1(A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_27])).

tff(c_121,plain,(
    ! [B_2,A_1] : m1_subset_1(k3_xboole_0(B_2,A_1),k1_zfmisc_1(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_265,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k1_tarski(A_53),k1_zfmisc_1(B_54))
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_121])).

tff(c_24,plain,(
    ~ m1_subset_1(k1_tarski('#skF_1'),k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_268,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_265,c_24])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:37:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.96/1.23  
% 1.96/1.23  %Foreground sorts:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Background operators:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Foreground operators:
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.23  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.96/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.23  
% 2.05/1.24  tff(f_54, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.05/1.24  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.05/1.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.05/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.05/1.24  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.05/1.24  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.05/1.24  tff(f_47, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.05/1.24  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.05/1.24  tff(c_82, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.05/1.24  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.24  tff(c_187, plain, (![A_49, B_50]: (k3_xboole_0(k1_tarski(A_49), B_50)=k1_tarski(A_49) | ~r2_hidden(A_49, B_50))), inference(resolution, [status(thm)], [c_82, c_6])).
% 2.05/1.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.24  tff(c_100, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.24  tff(c_22, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.24  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(k6_subset_1(A_17, B_18), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.24  tff(c_27, plain, (![A_17, B_18]: (m1_subset_1(k4_xboole_0(A_17, B_18), k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 2.05/1.24  tff(c_118, plain, (![A_38, B_39]: (m1_subset_1(k3_xboole_0(A_38, B_39), k1_zfmisc_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_27])).
% 2.05/1.24  tff(c_121, plain, (![B_2, A_1]: (m1_subset_1(k3_xboole_0(B_2, A_1), k1_zfmisc_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_118])).
% 2.05/1.24  tff(c_265, plain, (![A_53, B_54]: (m1_subset_1(k1_tarski(A_53), k1_zfmisc_1(B_54)) | ~r2_hidden(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_187, c_121])).
% 2.05/1.24  tff(c_24, plain, (~m1_subset_1(k1_tarski('#skF_1'), k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.05/1.24  tff(c_268, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_265, c_24])).
% 2.05/1.24  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_268])).
% 2.05/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  Inference rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Ref     : 0
% 2.05/1.24  #Sup     : 60
% 2.05/1.24  #Fact    : 0
% 2.05/1.24  #Define  : 0
% 2.05/1.24  #Split   : 0
% 2.05/1.24  #Chain   : 0
% 2.05/1.24  #Close   : 0
% 2.05/1.24  
% 2.05/1.24  Ordering : KBO
% 2.05/1.24  
% 2.05/1.24  Simplification rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Subsume      : 4
% 2.05/1.24  #Demod        : 8
% 2.05/1.24  #Tautology    : 35
% 2.05/1.24  #SimpNegUnit  : 0
% 2.05/1.24  #BackRed      : 0
% 2.05/1.24  
% 2.05/1.24  #Partial instantiations: 0
% 2.05/1.24  #Strategies tried      : 1
% 2.05/1.24  
% 2.05/1.24  Timing (in seconds)
% 2.05/1.24  ----------------------
% 2.05/1.25  Preprocessing        : 0.29
% 2.05/1.25  Parsing              : 0.16
% 2.05/1.25  CNF conversion       : 0.02
% 2.05/1.25  Main loop            : 0.16
% 2.05/1.25  Inferencing          : 0.06
% 2.05/1.25  Reduction            : 0.05
% 2.05/1.25  Demodulation         : 0.04
% 2.05/1.25  BG Simplification    : 0.01
% 2.05/1.25  Subsumption          : 0.02
% 2.05/1.25  Abstraction          : 0.01
% 2.05/1.25  MUC search           : 0.00
% 2.05/1.25  Cooper               : 0.00
% 2.05/1.25  Total                : 0.47
% 2.05/1.25  Index Insertion      : 0.00
% 2.05/1.25  Index Deletion       : 0.00
% 2.05/1.25  Index Matching       : 0.00
% 2.05/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
