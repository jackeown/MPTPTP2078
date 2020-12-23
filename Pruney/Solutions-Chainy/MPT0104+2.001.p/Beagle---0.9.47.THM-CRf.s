%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:46 EST 2020

% Result     : Theorem 29.23s
% Output     : CNFRefutation 29.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  85 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  99 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_20,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_191,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_213,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_393,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(A_43,k2_xboole_0(B_44,C_45))
      | ~ r1_tarski(k4_xboole_0(A_43,B_44),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_430,plain,(
    ! [A_46,B_47] : r1_tarski(A_46,k2_xboole_0(B_47,A_46)) ),
    inference(resolution,[status(thm)],[c_14,c_393])).

tff(c_494,plain,(
    ! [A_48] : r1_tarski(A_48,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_430])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_652,plain,(
    ! [A_53] : k4_xboole_0(A_53,A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_494,c_8])).

tff(c_220,plain,(
    ! [A_35,B_36] : k2_xboole_0(k4_xboole_0(A_35,B_36),A_35) = A_35 ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_226,plain,(
    ! [A_35,B_36] : k2_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_2])).

tff(c_667,plain,(
    ! [A_53] : k2_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_226])).

tff(c_507,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_494,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_214,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_191])).

tff(c_24,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_215,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_191])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_570,plain,(
    ! [A_50,B_51,C_52] : k4_xboole_0(k4_xboole_0(A_50,B_51),C_52) = k4_xboole_0(A_50,k2_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1410,plain,(
    ! [A_71,B_72,C_73] : r1_tarski(k4_xboole_0(A_71,k2_xboole_0(B_72,C_73)),k4_xboole_0(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_14])).

tff(c_1464,plain,(
    ! [A_13,B_14,B_72,C_73] : r1_tarski(k4_xboole_0(A_13,k2_xboole_0(B_14,k2_xboole_0(B_72,C_73))),k4_xboole_0(k4_xboole_0(A_13,B_14),B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1410])).

tff(c_44545,plain,(
    ! [A_379,B_380,B_381,C_382] : r1_tarski(k4_xboole_0(A_379,k2_xboole_0(B_380,k2_xboole_0(B_381,C_382))),k4_xboole_0(A_379,k2_xboole_0(B_380,B_381))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1464])).

tff(c_45377,plain,(
    ! [A_383,B_384] : r1_tarski(k4_xboole_0(A_383,k2_xboole_0(B_384,'#skF_3')),k4_xboole_0(A_383,k2_xboole_0(B_384,k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_44545])).

tff(c_45708,plain,(
    ! [A_383] : r1_tarski(k4_xboole_0(A_383,'#skF_3'),k4_xboole_0(A_383,k2_xboole_0(k4_xboole_0('#skF_2','#skF_1'),k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_45377])).

tff(c_94084,plain,(
    ! [A_526] : r1_tarski(k4_xboole_0(A_526,'#skF_3'),k4_xboole_0(A_526,k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_45708])).

tff(c_94189,plain,(
    r1_tarski(k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_94084])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_tarski(A_16,k2_xboole_0(B_17,C_18))
      | ~ r1_tarski(k4_xboole_0(A_16,B_17),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94246,plain,(
    r1_tarski(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_94189,c_18])).

tff(c_94254,plain,(
    r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_94246])).

tff(c_94256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_94254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.23/20.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.23/20.94  
% 29.23/20.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.23/20.94  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 29.23/20.94  
% 29.23/20.94  %Foreground sorts:
% 29.23/20.94  
% 29.23/20.94  
% 29.23/20.94  %Background operators:
% 29.23/20.94  
% 29.23/20.94  
% 29.23/20.94  %Foreground operators:
% 29.23/20.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.23/20.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.23/20.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.23/20.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 29.23/20.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.23/20.94  tff('#skF_2', type, '#skF_2': $i).
% 29.23/20.94  tff('#skF_3', type, '#skF_3': $i).
% 29.23/20.94  tff('#skF_1', type, '#skF_1': $i).
% 29.23/20.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.23/20.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.23/20.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.23/20.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.23/20.94  
% 29.23/20.96  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 29.23/20.96  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 29.23/20.96  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 29.23/20.96  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 29.23/20.96  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 29.23/20.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 29.23/20.96  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 29.23/20.96  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 29.23/20.96  tff(c_20, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.23/20.96  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.23/20.96  tff(c_191, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.23/20.96  tff(c_213, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), A_11)=A_11)), inference(resolution, [status(thm)], [c_14, c_191])).
% 29.23/20.96  tff(c_393, plain, (![A_43, B_44, C_45]: (r1_tarski(A_43, k2_xboole_0(B_44, C_45)) | ~r1_tarski(k4_xboole_0(A_43, B_44), C_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.23/20.96  tff(c_430, plain, (![A_46, B_47]: (r1_tarski(A_46, k2_xboole_0(B_47, A_46)))), inference(resolution, [status(thm)], [c_14, c_393])).
% 29.23/20.96  tff(c_494, plain, (![A_48]: (r1_tarski(A_48, A_48))), inference(superposition, [status(thm), theory('equality')], [c_213, c_430])).
% 29.23/20.96  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.23/20.96  tff(c_652, plain, (![A_53]: (k4_xboole_0(A_53, A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_494, c_8])).
% 29.23/20.96  tff(c_220, plain, (![A_35, B_36]: (k2_xboole_0(k4_xboole_0(A_35, B_36), A_35)=A_35)), inference(resolution, [status(thm)], [c_14, c_191])).
% 29.23/20.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.23/20.96  tff(c_226, plain, (![A_35, B_36]: (k2_xboole_0(A_35, k4_xboole_0(A_35, B_36))=A_35)), inference(superposition, [status(thm), theory('equality')], [c_220, c_2])).
% 29.23/20.96  tff(c_667, plain, (![A_53]: (k2_xboole_0(A_53, k1_xboole_0)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_652, c_226])).
% 29.23/20.96  tff(c_507, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_494, c_8])).
% 29.23/20.96  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.23/20.96  tff(c_22, plain, (r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.23/20.96  tff(c_214, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_22, c_191])).
% 29.23/20.96  tff(c_24, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.23/20.96  tff(c_215, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_24, c_191])).
% 29.23/20.96  tff(c_16, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.23/20.96  tff(c_570, plain, (![A_50, B_51, C_52]: (k4_xboole_0(k4_xboole_0(A_50, B_51), C_52)=k4_xboole_0(A_50, k2_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.23/20.96  tff(c_1410, plain, (![A_71, B_72, C_73]: (r1_tarski(k4_xboole_0(A_71, k2_xboole_0(B_72, C_73)), k4_xboole_0(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_570, c_14])).
% 29.23/20.96  tff(c_1464, plain, (![A_13, B_14, B_72, C_73]: (r1_tarski(k4_xboole_0(A_13, k2_xboole_0(B_14, k2_xboole_0(B_72, C_73))), k4_xboole_0(k4_xboole_0(A_13, B_14), B_72)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1410])).
% 29.23/20.96  tff(c_44545, plain, (![A_379, B_380, B_381, C_382]: (r1_tarski(k4_xboole_0(A_379, k2_xboole_0(B_380, k2_xboole_0(B_381, C_382))), k4_xboole_0(A_379, k2_xboole_0(B_380, B_381))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1464])).
% 29.23/20.96  tff(c_45377, plain, (![A_383, B_384]: (r1_tarski(k4_xboole_0(A_383, k2_xboole_0(B_384, '#skF_3')), k4_xboole_0(A_383, k2_xboole_0(B_384, k4_xboole_0('#skF_1', '#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_215, c_44545])).
% 29.23/20.96  tff(c_45708, plain, (![A_383]: (r1_tarski(k4_xboole_0(A_383, '#skF_3'), k4_xboole_0(A_383, k2_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), k4_xboole_0('#skF_1', '#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_214, c_45377])).
% 29.23/20.96  tff(c_94084, plain, (![A_526]: (r1_tarski(k4_xboole_0(A_526, '#skF_3'), k4_xboole_0(A_526, k5_xboole_0('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_45708])).
% 29.23/20.96  tff(c_94189, plain, (r1_tarski(k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_507, c_94084])).
% 29.23/20.96  tff(c_18, plain, (![A_16, B_17, C_18]: (r1_tarski(A_16, k2_xboole_0(B_17, C_18)) | ~r1_tarski(k4_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.23/20.96  tff(c_94246, plain, (r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_94189, c_18])).
% 29.23/20.96  tff(c_94254, plain, (r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_667, c_94246])).
% 29.23/20.96  tff(c_94256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_94254])).
% 29.23/20.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.23/20.96  
% 29.23/20.96  Inference rules
% 29.23/20.96  ----------------------
% 29.23/20.96  #Ref     : 0
% 29.23/20.96  #Sup     : 23750
% 29.23/20.96  #Fact    : 0
% 29.23/20.96  #Define  : 0
% 29.23/20.96  #Split   : 2
% 29.23/20.96  #Chain   : 0
% 29.23/20.96  #Close   : 0
% 29.23/20.96  
% 29.23/20.96  Ordering : KBO
% 29.23/20.96  
% 29.23/20.96  Simplification rules
% 29.23/20.96  ----------------------
% 29.23/20.96  #Subsume      : 220
% 29.23/20.96  #Demod        : 30747
% 29.23/20.96  #Tautology    : 12626
% 29.23/20.96  #SimpNegUnit  : 1
% 29.23/20.96  #BackRed      : 13
% 29.23/20.96  
% 29.23/20.96  #Partial instantiations: 0
% 29.23/20.96  #Strategies tried      : 1
% 29.23/20.96  
% 29.23/20.96  Timing (in seconds)
% 29.23/20.96  ----------------------
% 29.23/20.96  Preprocessing        : 0.28
% 29.23/20.96  Parsing              : 0.16
% 29.23/20.96  CNF conversion       : 0.02
% 29.23/20.96  Main loop            : 19.91
% 29.23/20.96  Inferencing          : 1.72
% 29.23/20.96  Reduction            : 13.74
% 29.23/20.96  Demodulation         : 12.89
% 29.23/20.96  BG Simplification    : 0.25
% 29.23/20.96  Subsumption          : 3.50
% 29.23/20.96  Abstraction          : 0.40
% 29.23/20.96  MUC search           : 0.00
% 29.23/20.96  Cooper               : 0.00
% 29.23/20.96  Total                : 20.21
% 29.23/20.96  Index Insertion      : 0.00
% 29.23/20.96  Index Deletion       : 0.00
% 29.23/20.96  Index Matching       : 0.00
% 29.23/20.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
