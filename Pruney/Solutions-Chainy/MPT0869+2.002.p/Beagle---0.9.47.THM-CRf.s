%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:26 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 109 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 ( 153 expanded)
%              Number of equality atoms :   47 ( 150 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
       => ( A = D
          & B = E
          & C = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_8,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_29,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_4,plain,(
    ! [A_4,B_5] : k1_mcart_1(k4_tarski(A_4,B_5)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_10,B_11,C_12] : k4_tarski(k4_tarski(A_10,B_11),C_12) = k3_mcart_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_10,B_11,C_12] : k1_mcart_1(k3_mcart_1(A_10,B_11,C_12)) = k4_tarski(A_10,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_10,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_3') = k3_mcart_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_mcart_1(k4_tarski(A_4,B_5)) = B_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_13,B_14,C_15] : k2_mcart_1(k3_mcart_1(A_13,B_14,C_15)) = C_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_64,plain,(
    k2_mcart_1(k3_mcart_1('#skF_4','#skF_5','#skF_6')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_55])).

tff(c_46,plain,(
    ! [A_10,B_11,C_12] : k2_mcart_1(k3_mcart_1(A_10,B_11,C_12)) = C_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_70,plain,(
    '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_46])).

tff(c_78,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_3') = k3_mcart_1('#skF_4','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10])).

tff(c_93,plain,(
    ! [A_16,B_17,C_18] : k1_mcart_1(k3_mcart_1(A_16,B_17,C_18)) = k4_tarski(A_16,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_102,plain,(
    k1_mcart_1(k3_mcart_1('#skF_4','#skF_5','#skF_3')) = k4_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_93])).

tff(c_105,plain,(
    k4_tarski('#skF_1','#skF_2') = k4_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_102])).

tff(c_112,plain,(
    k1_mcart_1(k4_tarski('#skF_4','#skF_5')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_4])).

tff(c_119,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_112])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_119])).

tff(c_122,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_128,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_134,plain,(
    ! [A_19,B_20,C_21] : k4_tarski(k4_tarski(A_19,B_20),C_21) = k3_mcart_1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_19,B_20,C_21] : k2_mcart_1(k3_mcart_1(A_19,B_20,C_21)) = C_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_6])).

tff(c_123,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_129,plain,(
    k3_mcart_1('#skF_4','#skF_5','#skF_6') = k3_mcart_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_10])).

tff(c_155,plain,(
    ! [A_22,B_23,C_24] : k2_mcart_1(k3_mcart_1(A_22,B_23,C_24)) = C_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_6])).

tff(c_164,plain,(
    k2_mcart_1(k3_mcart_1('#skF_4','#skF_2','#skF_3')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_155])).

tff(c_167,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_167])).

tff(c_170,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_186,plain,(
    ! [A_25,B_26,C_27] : k4_tarski(k4_tarski(A_25,B_26),C_27) = k3_mcart_1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_195,plain,(
    ! [A_25,B_26,C_27] : k1_mcart_1(k3_mcart_1(A_25,B_26,C_27)) = k4_tarski(A_25,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_4])).

tff(c_171,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_172,plain,(
    k3_mcart_1('#skF_4','#skF_5','#skF_6') = k3_mcart_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_10])).

tff(c_177,plain,(
    k3_mcart_1('#skF_4','#skF_5','#skF_3') = k3_mcart_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_172])).

tff(c_220,plain,(
    ! [A_31,B_32,C_33] : k1_mcart_1(k3_mcart_1(A_31,B_32,C_33)) = k4_tarski(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_4])).

tff(c_229,plain,(
    k1_mcart_1(k3_mcart_1('#skF_4','#skF_2','#skF_3')) = k4_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_220])).

tff(c_232,plain,(
    k4_tarski('#skF_4','#skF_5') = k4_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_229])).

tff(c_242,plain,(
    k2_mcart_1(k4_tarski('#skF_4','#skF_2')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_6])).

tff(c_247,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_242])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  %$ k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.80/1.16  
% 1.80/1.16  %Foreground sorts:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Background operators:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Foreground operators:
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.80/1.16  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.80/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.80/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.80/1.16  
% 1.80/1.17  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_mcart_1)).
% 1.80/1.17  tff(f_31, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.80/1.17  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.80/1.17  tff(c_8, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.80/1.17  tff(c_29, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_8])).
% 1.80/1.17  tff(c_4, plain, (![A_4, B_5]: (k1_mcart_1(k4_tarski(A_4, B_5))=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.17  tff(c_34, plain, (![A_10, B_11, C_12]: (k4_tarski(k4_tarski(A_10, B_11), C_12)=k3_mcart_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.17  tff(c_43, plain, (![A_10, B_11, C_12]: (k1_mcart_1(k3_mcart_1(A_10, B_11, C_12))=k4_tarski(A_10, B_11))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4])).
% 1.80/1.17  tff(c_10, plain, (k3_mcart_1('#skF_1', '#skF_2', '#skF_3')=k3_mcart_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.80/1.17  tff(c_6, plain, (![A_4, B_5]: (k2_mcart_1(k4_tarski(A_4, B_5))=B_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.17  tff(c_55, plain, (![A_13, B_14, C_15]: (k2_mcart_1(k3_mcart_1(A_13, B_14, C_15))=C_15)), inference(superposition, [status(thm), theory('equality')], [c_34, c_6])).
% 1.80/1.17  tff(c_64, plain, (k2_mcart_1(k3_mcart_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10, c_55])).
% 1.80/1.17  tff(c_46, plain, (![A_10, B_11, C_12]: (k2_mcart_1(k3_mcart_1(A_10, B_11, C_12))=C_12)), inference(superposition, [status(thm), theory('equality')], [c_34, c_6])).
% 1.80/1.17  tff(c_70, plain, ('#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_64, c_46])).
% 1.80/1.17  tff(c_78, plain, (k3_mcart_1('#skF_1', '#skF_2', '#skF_3')=k3_mcart_1('#skF_4', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10])).
% 1.80/1.17  tff(c_93, plain, (![A_16, B_17, C_18]: (k1_mcart_1(k3_mcart_1(A_16, B_17, C_18))=k4_tarski(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4])).
% 1.80/1.17  tff(c_102, plain, (k1_mcart_1(k3_mcart_1('#skF_4', '#skF_5', '#skF_3'))=k4_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_78, c_93])).
% 1.80/1.17  tff(c_105, plain, (k4_tarski('#skF_1', '#skF_2')=k4_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_102])).
% 1.80/1.17  tff(c_112, plain, (k1_mcart_1(k4_tarski('#skF_4', '#skF_5'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_105, c_4])).
% 1.80/1.17  tff(c_119, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_112])).
% 1.80/1.17  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_119])).
% 1.80/1.17  tff(c_122, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_8])).
% 1.80/1.17  tff(c_128, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_122])).
% 1.80/1.17  tff(c_134, plain, (![A_19, B_20, C_21]: (k4_tarski(k4_tarski(A_19, B_20), C_21)=k3_mcart_1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.17  tff(c_146, plain, (![A_19, B_20, C_21]: (k2_mcart_1(k3_mcart_1(A_19, B_20, C_21))=C_21)), inference(superposition, [status(thm), theory('equality')], [c_134, c_6])).
% 1.80/1.17  tff(c_123, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_8])).
% 1.80/1.17  tff(c_129, plain, (k3_mcart_1('#skF_4', '#skF_5', '#skF_6')=k3_mcart_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_10])).
% 1.80/1.17  tff(c_155, plain, (![A_22, B_23, C_24]: (k2_mcart_1(k3_mcart_1(A_22, B_23, C_24))=C_24)), inference(superposition, [status(thm), theory('equality')], [c_134, c_6])).
% 1.80/1.17  tff(c_164, plain, (k2_mcart_1(k3_mcart_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_129, c_155])).
% 1.80/1.17  tff(c_167, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_164])).
% 1.80/1.17  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_167])).
% 1.80/1.17  tff(c_170, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_122])).
% 1.80/1.17  tff(c_186, plain, (![A_25, B_26, C_27]: (k4_tarski(k4_tarski(A_25, B_26), C_27)=k3_mcart_1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.17  tff(c_195, plain, (![A_25, B_26, C_27]: (k1_mcart_1(k3_mcart_1(A_25, B_26, C_27))=k4_tarski(A_25, B_26))), inference(superposition, [status(thm), theory('equality')], [c_186, c_4])).
% 1.80/1.17  tff(c_171, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_122])).
% 1.80/1.17  tff(c_172, plain, (k3_mcart_1('#skF_4', '#skF_5', '#skF_6')=k3_mcart_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_10])).
% 1.80/1.17  tff(c_177, plain, (k3_mcart_1('#skF_4', '#skF_5', '#skF_3')=k3_mcart_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_172])).
% 1.80/1.17  tff(c_220, plain, (![A_31, B_32, C_33]: (k1_mcart_1(k3_mcart_1(A_31, B_32, C_33))=k4_tarski(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_186, c_4])).
% 1.80/1.17  tff(c_229, plain, (k1_mcart_1(k3_mcart_1('#skF_4', '#skF_2', '#skF_3'))=k4_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_177, c_220])).
% 1.80/1.17  tff(c_232, plain, (k4_tarski('#skF_4', '#skF_5')=k4_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_229])).
% 1.80/1.17  tff(c_242, plain, (k2_mcart_1(k4_tarski('#skF_4', '#skF_2'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_232, c_6])).
% 1.80/1.17  tff(c_247, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_242])).
% 1.80/1.17  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_247])).
% 1.80/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  Inference rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Ref     : 0
% 1.80/1.17  #Sup     : 68
% 1.80/1.17  #Fact    : 0
% 1.80/1.17  #Define  : 0
% 1.80/1.17  #Split   : 2
% 1.80/1.17  #Chain   : 0
% 1.80/1.17  #Close   : 0
% 1.80/1.17  
% 1.80/1.17  Ordering : KBO
% 1.80/1.17  
% 1.80/1.17  Simplification rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Subsume      : 0
% 1.80/1.17  #Demod        : 17
% 1.80/1.17  #Tautology    : 45
% 1.80/1.17  #SimpNegUnit  : 3
% 1.80/1.17  #BackRed      : 3
% 1.80/1.17  
% 1.80/1.17  #Partial instantiations: 0
% 1.80/1.17  #Strategies tried      : 1
% 1.80/1.17  
% 1.80/1.17  Timing (in seconds)
% 1.80/1.17  ----------------------
% 1.80/1.18  Preprocessing        : 0.26
% 1.80/1.18  Parsing              : 0.14
% 1.80/1.18  CNF conversion       : 0.02
% 1.80/1.18  Main loop            : 0.15
% 1.80/1.18  Inferencing          : 0.06
% 1.80/1.18  Reduction            : 0.05
% 1.80/1.18  Demodulation         : 0.04
% 1.80/1.18  BG Simplification    : 0.01
% 1.80/1.18  Subsumption          : 0.01
% 1.80/1.18  Abstraction          : 0.01
% 1.80/1.18  MUC search           : 0.00
% 1.80/1.18  Cooper               : 0.00
% 1.80/1.18  Total                : 0.44
% 1.80/1.18  Index Insertion      : 0.00
% 1.80/1.18  Index Deletion       : 0.00
% 1.80/1.18  Index Matching       : 0.00
% 1.80/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
