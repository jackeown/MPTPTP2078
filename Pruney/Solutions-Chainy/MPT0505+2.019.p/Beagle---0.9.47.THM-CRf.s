%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:53 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    3
%              Number of atoms          :   20 (  26 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [C_12,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_12,A_13),B_14) = k7_relat_1(C_12,k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50,c_2,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.69/1.17  
% 1.69/1.17  %Foreground sorts:
% 1.69/1.17  
% 1.69/1.17  
% 1.69/1.17  %Background operators:
% 1.69/1.17  
% 1.69/1.17  
% 1.69/1.17  %Foreground operators:
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.69/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.69/1.17  
% 1.74/1.18  tff(f_42, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 1.74/1.18  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.74/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.74/1.18  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.74/1.18  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.18  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.18  tff(c_46, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.18  tff(c_50, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_10, c_46])).
% 1.74/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.74/1.18  tff(c_55, plain, (![C_12, A_13, B_14]: (k7_relat_1(k7_relat_1(C_12, A_13), B_14)=k7_relat_1(C_12, k3_xboole_0(A_13, B_14)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.74/1.18  tff(c_8, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.18  tff(c_64, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 1.74/1.18  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_50, c_2, c_64])).
% 1.74/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  Inference rules
% 1.74/1.18  ----------------------
% 1.74/1.18  #Ref     : 0
% 1.74/1.18  #Sup     : 16
% 1.74/1.18  #Fact    : 0
% 1.74/1.18  #Define  : 0
% 1.74/1.18  #Split   : 0
% 1.74/1.18  #Chain   : 0
% 1.74/1.18  #Close   : 0
% 1.74/1.18  
% 1.74/1.18  Ordering : KBO
% 1.74/1.18  
% 1.74/1.18  Simplification rules
% 1.74/1.18  ----------------------
% 1.74/1.18  #Subsume      : 0
% 1.74/1.18  #Demod        : 3
% 1.74/1.18  #Tautology    : 11
% 1.74/1.18  #SimpNegUnit  : 0
% 1.74/1.18  #BackRed      : 0
% 1.74/1.18  
% 1.74/1.18  #Partial instantiations: 0
% 1.74/1.18  #Strategies tried      : 1
% 1.74/1.18  
% 1.74/1.18  Timing (in seconds)
% 1.74/1.18  ----------------------
% 1.74/1.18  Preprocessing        : 0.27
% 1.74/1.18  Parsing              : 0.15
% 1.74/1.18  CNF conversion       : 0.02
% 1.74/1.18  Main loop            : 0.09
% 1.74/1.18  Inferencing          : 0.04
% 1.74/1.18  Reduction            : 0.03
% 1.74/1.18  Demodulation         : 0.02
% 1.74/1.18  BG Simplification    : 0.01
% 1.74/1.18  Subsumption          : 0.01
% 1.74/1.18  Abstraction          : 0.00
% 1.74/1.18  MUC search           : 0.00
% 1.74/1.18  Cooper               : 0.00
% 1.74/1.18  Total                : 0.38
% 1.74/1.18  Index Insertion      : 0.00
% 1.74/1.18  Index Deletion       : 0.00
% 1.74/1.18  Index Matching       : 0.00
% 1.74/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
