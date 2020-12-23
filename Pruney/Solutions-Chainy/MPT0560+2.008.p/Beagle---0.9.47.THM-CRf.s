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
% DateTime   : Thu Dec  3 10:01:11 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  53 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_51,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_88,plain,(
    ! [C_22,A_23,B_24] :
      ( k7_relat_1(k7_relat_1(C_22,A_23),B_24) = k7_relat_1(C_22,k3_xboole_0(A_23,B_24))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [C_25,A_26,B_27] :
      ( k2_relat_1(k7_relat_1(C_25,k3_xboole_0(A_26,B_27))) = k9_relat_1(k7_relat_1(C_25,A_26),B_27)
      | ~ v1_relat_1(k7_relat_1(C_25,A_26))
      | ~ v1_relat_1(C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_10])).

tff(c_225,plain,(
    ! [C_34] :
      ( k9_relat_1(k7_relat_1(C_34,'#skF_3'),'#skF_2') = k2_relat_1(k7_relat_1(C_34,'#skF_2'))
      | ~ v1_relat_1(k7_relat_1(C_34,'#skF_3'))
      | ~ v1_relat_1(C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_109])).

tff(c_239,plain,(
    ! [A_35] :
      ( k9_relat_1(k7_relat_1(A_35,'#skF_3'),'#skF_2') = k2_relat_1(k7_relat_1(A_35,'#skF_2'))
      | ~ v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_225])).

tff(c_12,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,
    ( k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_12])).

tff(c_259,plain,(
    k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_245])).

tff(c_263,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_259])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_263])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 09:19:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.08/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.27  
% 2.08/1.28  tff(f_51, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.08/1.28  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.08/1.28  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.08/1.28  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.08/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.08/1.28  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.08/1.28  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.28  tff(c_10, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.28  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.28  tff(c_14, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.28  tff(c_51, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.28  tff(c_55, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_51])).
% 2.08/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.28  tff(c_59, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 2.08/1.28  tff(c_88, plain, (![C_22, A_23, B_24]: (k7_relat_1(k7_relat_1(C_22, A_23), B_24)=k7_relat_1(C_22, k3_xboole_0(A_23, B_24)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.28  tff(c_109, plain, (![C_25, A_26, B_27]: (k2_relat_1(k7_relat_1(C_25, k3_xboole_0(A_26, B_27)))=k9_relat_1(k7_relat_1(C_25, A_26), B_27) | ~v1_relat_1(k7_relat_1(C_25, A_26)) | ~v1_relat_1(C_25))), inference(superposition, [status(thm), theory('equality')], [c_88, c_10])).
% 2.08/1.28  tff(c_225, plain, (![C_34]: (k9_relat_1(k7_relat_1(C_34, '#skF_3'), '#skF_2')=k2_relat_1(k7_relat_1(C_34, '#skF_2')) | ~v1_relat_1(k7_relat_1(C_34, '#skF_3')) | ~v1_relat_1(C_34))), inference(superposition, [status(thm), theory('equality')], [c_59, c_109])).
% 2.08/1.28  tff(c_239, plain, (![A_35]: (k9_relat_1(k7_relat_1(A_35, '#skF_3'), '#skF_2')=k2_relat_1(k7_relat_1(A_35, '#skF_2')) | ~v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_6, c_225])).
% 2.08/1.28  tff(c_12, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.28  tff(c_245, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_239, c_12])).
% 2.08/1.28  tff(c_259, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_245])).
% 2.08/1.28  tff(c_263, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_259])).
% 2.08/1.28  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_263])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 65
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 0
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 4
% 2.08/1.28  #Demod        : 5
% 2.08/1.28  #Tautology    : 27
% 2.08/1.28  #SimpNegUnit  : 0
% 2.08/1.28  #BackRed      : 0
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.26
% 2.08/1.28  Parsing              : 0.14
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.22
% 2.08/1.28  Inferencing          : 0.09
% 2.08/1.28  Reduction            : 0.07
% 2.08/1.28  Demodulation         : 0.05
% 2.08/1.28  BG Simplification    : 0.01
% 2.08/1.28  Subsumption          : 0.04
% 2.08/1.28  Abstraction          : 0.01
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.51
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
