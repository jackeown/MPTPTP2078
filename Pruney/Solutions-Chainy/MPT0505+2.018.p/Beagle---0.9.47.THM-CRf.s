%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:53 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  42 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( k7_relat_1(k7_relat_1(C_5,A_3),B_4) = k7_relat_1(C_5,k3_xboole_0(A_3,B_4))
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [C_14,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_14,A_15),B_16) = k7_relat_1(C_14,A_15)
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [C_17,A_18,B_19] :
      ( k7_relat_1(C_17,k3_xboole_0(A_18,B_19)) = k7_relat_1(C_17,A_18)
      | ~ r1_tarski(A_18,B_19)
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [C_11,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_11,A_12),B_13) = k7_relat_1(C_11,k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_55,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_64,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2,c_55])).

tff(c_105,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_64])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.26  
% 1.84/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.26  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.84/1.26  
% 1.84/1.26  %Foreground sorts:
% 1.84/1.26  
% 1.84/1.26  
% 1.84/1.26  %Background operators:
% 1.84/1.26  
% 1.84/1.26  
% 1.84/1.26  %Foreground operators:
% 1.84/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.84/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.26  
% 1.84/1.27  tff(f_44, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 1.84/1.27  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.84/1.27  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.84/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.84/1.27  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.27  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.27  tff(c_4, plain, (![C_5, A_3, B_4]: (k7_relat_1(k7_relat_1(C_5, A_3), B_4)=k7_relat_1(C_5, k3_xboole_0(A_3, B_4)) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.27  tff(c_66, plain, (![C_14, A_15, B_16]: (k7_relat_1(k7_relat_1(C_14, A_15), B_16)=k7_relat_1(C_14, A_15) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.27  tff(c_99, plain, (![C_17, A_18, B_19]: (k7_relat_1(C_17, k3_xboole_0(A_18, B_19))=k7_relat_1(C_17, A_18) | ~r1_tarski(A_18, B_19) | ~v1_relat_1(C_17) | ~v1_relat_1(C_17))), inference(superposition, [status(thm), theory('equality')], [c_4, c_66])).
% 1.84/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.27  tff(c_46, plain, (![C_11, A_12, B_13]: (k7_relat_1(k7_relat_1(C_11, A_12), B_13)=k7_relat_1(C_11, k3_xboole_0(A_12, B_13)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.27  tff(c_8, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.27  tff(c_55, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_8])).
% 1.84/1.27  tff(c_64, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2, c_55])).
% 1.84/1.27  tff(c_105, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_99, c_64])).
% 1.84/1.27  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_105])).
% 1.84/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.27  
% 1.84/1.27  Inference rules
% 1.84/1.27  ----------------------
% 1.84/1.27  #Ref     : 0
% 1.84/1.27  #Sup     : 33
% 1.84/1.27  #Fact    : 0
% 1.84/1.27  #Define  : 0
% 1.84/1.27  #Split   : 1
% 1.84/1.27  #Chain   : 0
% 1.84/1.27  #Close   : 0
% 1.84/1.27  
% 1.84/1.27  Ordering : KBO
% 1.84/1.27  
% 1.84/1.27  Simplification rules
% 1.84/1.27  ----------------------
% 1.84/1.27  #Subsume      : 0
% 1.84/1.27  #Demod        : 5
% 1.84/1.27  #Tautology    : 13
% 1.84/1.27  #SimpNegUnit  : 0
% 1.84/1.27  #BackRed      : 0
% 1.84/1.27  
% 1.84/1.27  #Partial instantiations: 0
% 1.84/1.27  #Strategies tried      : 1
% 1.84/1.27  
% 1.84/1.27  Timing (in seconds)
% 1.84/1.27  ----------------------
% 1.84/1.27  Preprocessing        : 0.32
% 1.84/1.27  Parsing              : 0.17
% 1.84/1.27  CNF conversion       : 0.02
% 1.84/1.27  Main loop            : 0.15
% 1.84/1.27  Inferencing          : 0.06
% 1.84/1.27  Reduction            : 0.05
% 1.84/1.27  Demodulation         : 0.04
% 1.84/1.27  BG Simplification    : 0.01
% 1.84/1.27  Subsumption          : 0.02
% 1.84/1.27  Abstraction          : 0.01
% 1.84/1.27  MUC search           : 0.00
% 1.84/1.27  Cooper               : 0.00
% 1.84/1.27  Total                : 0.49
% 1.84/1.27  Index Insertion      : 0.00
% 1.84/1.27  Index Deletion       : 0.00
% 1.84/1.27  Index Matching       : 0.00
% 1.84/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
