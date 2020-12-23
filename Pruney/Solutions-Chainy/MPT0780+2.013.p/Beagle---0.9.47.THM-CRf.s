%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:41 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
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
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_wellord1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

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
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

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
      ( k2_wellord1(k2_wellord1(C_12,A_13),B_14) = k2_wellord1(C_12,k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50,c_2,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n012.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 20:48:52 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.06  
% 1.63/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.06  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_wellord1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.63/1.06  
% 1.63/1.06  %Foreground sorts:
% 1.63/1.06  
% 1.63/1.06  
% 1.63/1.06  %Background operators:
% 1.63/1.06  
% 1.63/1.06  
% 1.63/1.06  %Foreground operators:
% 1.63/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.06  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.63/1.06  
% 1.63/1.06  tff(f_42, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 1.63/1.06  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.63/1.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.63/1.06  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 1.63/1.06  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.06  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.06  tff(c_46, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.06  tff(c_50, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_10, c_46])).
% 1.63/1.06  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.06  tff(c_55, plain, (![C_12, A_13, B_14]: (k2_wellord1(k2_wellord1(C_12, A_13), B_14)=k2_wellord1(C_12, k3_xboole_0(A_13, B_14)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.06  tff(c_8, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.06  tff(c_64, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 1.63/1.06  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_50, c_2, c_64])).
% 1.63/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.06  
% 1.63/1.06  Inference rules
% 1.63/1.06  ----------------------
% 1.63/1.06  #Ref     : 0
% 1.63/1.06  #Sup     : 16
% 1.63/1.06  #Fact    : 0
% 1.63/1.06  #Define  : 0
% 1.63/1.06  #Split   : 0
% 1.63/1.06  #Chain   : 0
% 1.63/1.06  #Close   : 0
% 1.63/1.06  
% 1.63/1.06  Ordering : KBO
% 1.63/1.06  
% 1.63/1.06  Simplification rules
% 1.63/1.06  ----------------------
% 1.63/1.06  #Subsume      : 0
% 1.63/1.06  #Demod        : 3
% 1.63/1.06  #Tautology    : 11
% 1.63/1.06  #SimpNegUnit  : 0
% 1.63/1.06  #BackRed      : 0
% 1.63/1.06  
% 1.63/1.06  #Partial instantiations: 0
% 1.63/1.06  #Strategies tried      : 1
% 1.63/1.06  
% 1.63/1.06  Timing (in seconds)
% 1.63/1.06  ----------------------
% 1.63/1.07  Preprocessing        : 0.25
% 1.63/1.07  Parsing              : 0.14
% 1.63/1.07  CNF conversion       : 0.01
% 1.63/1.07  Main loop            : 0.09
% 1.63/1.07  Inferencing          : 0.04
% 1.63/1.07  Reduction            : 0.02
% 1.63/1.07  Demodulation         : 0.02
% 1.63/1.07  BG Simplification    : 0.01
% 1.63/1.07  Subsumption          : 0.01
% 1.63/1.07  Abstraction          : 0.00
% 1.63/1.07  MUC search           : 0.00
% 1.63/1.07  Cooper               : 0.00
% 1.63/1.07  Total                : 0.36
% 1.63/1.07  Index Insertion      : 0.00
% 1.63/1.07  Index Deletion       : 0.00
% 1.63/1.07  Index Matching       : 0.00
% 1.63/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
