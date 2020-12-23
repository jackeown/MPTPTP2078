%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:20 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  39 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k8_relat_1(B,A))
        & v1_relat_1(k8_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_20,plain,(
    k8_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( v1_xboole_0(k8_relat_1(B_12,A_11))
      | ~ v1_xboole_0(B_12)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_2'(A_21,B_22),A_21)
      | r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_26,B_27] :
      ( ~ v1_xboole_0(A_26)
      | r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_50,c_14])).

tff(c_66,plain,(
    ! [B_29,A_30] :
      ( k8_relat_1(B_29,A_30) = k1_xboole_0
      | ~ v1_xboole_0(B_29)
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_18,c_56])).

tff(c_73,plain,(
    ! [A_31] :
      ( k8_relat_1(k1_xboole_0,A_31) = k1_xboole_0
      | ~ v1_relat_1(A_31) ) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_79,plain,(
    k8_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:15:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.17  
% 1.67/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.17  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.67/1.17  
% 1.67/1.17  %Foreground sorts:
% 1.67/1.17  
% 1.67/1.17  
% 1.67/1.17  %Background operators:
% 1.67/1.17  
% 1.67/1.17  
% 1.67/1.17  %Foreground operators:
% 1.67/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.67/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.67/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.67/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.17  
% 1.85/1.18  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.85/1.18  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.85/1.18  tff(f_51, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k8_relat_1(B, A)) & v1_relat_1(k8_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc18_relat_1)).
% 1.85/1.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.85/1.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.85/1.18  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.85/1.18  tff(c_20, plain, (k8_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.85/1.18  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.85/1.18  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.85/1.18  tff(c_18, plain, (![B_12, A_11]: (v1_xboole_0(k8_relat_1(B_12, A_11)) | ~v1_xboole_0(B_12) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.85/1.18  tff(c_32, plain, (![A_21, B_22]: (r2_hidden('#skF_2'(A_21, B_22), A_21) | r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.18  tff(c_50, plain, (![A_26, B_27]: (~v1_xboole_0(A_26) | r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_32, c_2])).
% 1.85/1.18  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.85/1.18  tff(c_56, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_50, c_14])).
% 1.85/1.18  tff(c_66, plain, (![B_29, A_30]: (k8_relat_1(B_29, A_30)=k1_xboole_0 | ~v1_xboole_0(B_29) | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_18, c_56])).
% 1.85/1.18  tff(c_73, plain, (![A_31]: (k8_relat_1(k1_xboole_0, A_31)=k1_xboole_0 | ~v1_relat_1(A_31))), inference(resolution, [status(thm)], [c_12, c_66])).
% 1.85/1.18  tff(c_79, plain, (k8_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_73])).
% 1.85/1.18  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_79])).
% 1.85/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  Inference rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Ref     : 0
% 1.85/1.18  #Sup     : 11
% 1.85/1.18  #Fact    : 0
% 1.85/1.18  #Define  : 0
% 1.85/1.18  #Split   : 0
% 1.85/1.18  #Chain   : 0
% 1.85/1.18  #Close   : 0
% 1.85/1.18  
% 1.85/1.18  Ordering : KBO
% 1.85/1.18  
% 1.85/1.18  Simplification rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Subsume      : 0
% 1.85/1.18  #Demod        : 0
% 1.85/1.18  #Tautology    : 3
% 1.85/1.18  #SimpNegUnit  : 1
% 1.85/1.18  #BackRed      : 0
% 1.85/1.18  
% 1.85/1.18  #Partial instantiations: 0
% 1.85/1.18  #Strategies tried      : 1
% 1.85/1.18  
% 1.85/1.18  Timing (in seconds)
% 1.85/1.18  ----------------------
% 1.85/1.18  Preprocessing        : 0.30
% 1.85/1.18  Parsing              : 0.17
% 1.85/1.18  CNF conversion       : 0.02
% 1.85/1.18  Main loop            : 0.11
% 1.85/1.18  Inferencing          : 0.05
% 1.85/1.18  Reduction            : 0.02
% 1.85/1.18  Demodulation         : 0.01
% 1.85/1.18  BG Simplification    : 0.01
% 1.85/1.18  Subsumption          : 0.02
% 1.85/1.18  Abstraction          : 0.00
% 1.85/1.18  MUC search           : 0.00
% 1.85/1.18  Cooper               : 0.00
% 1.85/1.18  Total                : 0.43
% 1.85/1.18  Index Insertion      : 0.00
% 1.85/1.18  Index Deletion       : 0.00
% 1.85/1.18  Index Matching       : 0.00
% 1.85/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
