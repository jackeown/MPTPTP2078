%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:25 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 125 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 214 expanded)
%              Number of equality atoms :   70 ( 211 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_mcart_1 > k4_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
       => ( A = D
          & B = E
          & C = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_8,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k4_tarski(k4_tarski(A_5,B_6),C_7) = k3_mcart_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_3') = k3_mcart_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] : k4_tarski(k4_tarski(A_16,B_17),C_18) = k3_mcart_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [D_4,B_2,C_3,A_1] :
      ( D_4 = B_2
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [C_23,A_20,B_21,A_22,B_19] :
      ( C_23 = B_21
      | k4_tarski(A_22,B_21) != k3_mcart_1(A_20,B_19,C_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_60,plain,(
    ! [B_24,A_25] :
      ( B_24 = '#skF_3'
      | k4_tarski(A_25,B_24) != k3_mcart_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_63,plain,(
    ! [C_7,A_5,B_6] :
      ( C_7 = '#skF_3'
      | k3_mcart_1(A_5,B_6,C_7) != k3_mcart_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_66,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_63])).

tff(c_75,plain,(
    k3_mcart_1('#skF_1','#skF_2','#skF_3') = k3_mcart_1('#skF_4','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10])).

tff(c_4,plain,(
    ! [C_3,A_1,D_4,B_2] :
      ( C_3 = A_1
      | k4_tarski(C_3,D_4) != k4_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [C_39,D_36,A_37,B_35,C_38] :
      ( k4_tarski(A_37,B_35) = C_38
      | k4_tarski(C_38,D_36) != k3_mcart_1(A_37,B_35,C_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_105,plain,(
    ! [C_40,D_41] :
      ( k4_tarski('#skF_1','#skF_2') = C_40
      | k4_tarski(C_40,D_41) != k3_mcart_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_98])).

tff(c_108,plain,(
    ! [A_5,B_6,C_7] :
      ( k4_tarski(A_5,B_6) = k4_tarski('#skF_1','#skF_2')
      | k3_mcart_1(A_5,B_6,C_7) != k3_mcart_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_105])).

tff(c_138,plain,(
    k4_tarski('#skF_1','#skF_2') = k4_tarski('#skF_4','#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_108])).

tff(c_160,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_2'
      | k4_tarski(A_1,B_2) != k4_tarski('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_2])).

tff(c_200,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_160])).

tff(c_169,plain,(
    ! [C_3,D_4] :
      ( C_3 = '#skF_1'
      | k4_tarski(C_3,D_4) != k4_tarski('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_4])).

tff(c_254,plain,(
    ! [C_3,D_4] :
      ( C_3 = '#skF_1'
      | k4_tarski(C_3,D_4) != k4_tarski('#skF_4','#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_169])).

tff(c_257,plain,(
    '#skF_1' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_254])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11,c_257])).

tff(c_260,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_266,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_261,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_267,plain,(
    k3_mcart_1('#skF_4','#skF_5','#skF_6') = k3_mcart_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_10])).

tff(c_282,plain,(
    ! [A_66,B_67,C_68] : k4_tarski(k4_tarski(A_66,B_67),C_68) = k3_mcart_1(A_66,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_309,plain,(
    ! [B_70,C_73,B_72,A_71,A_69] :
      ( C_73 = B_70
      | k4_tarski(A_71,B_70) != k3_mcart_1(A_69,B_72,C_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_2])).

tff(c_316,plain,(
    ! [B_74,A_75] :
      ( B_74 = '#skF_6'
      | k4_tarski(A_75,B_74) != k3_mcart_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_309])).

tff(c_319,plain,(
    ! [C_7,A_5,B_6] :
      ( C_7 = '#skF_6'
      | k3_mcart_1(A_5,B_6,C_7) != k3_mcart_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_316])).

tff(c_333,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_319])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_333])).

tff(c_336,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_337,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_338,plain,(
    k3_mcart_1('#skF_4','#skF_5','#skF_6') = k3_mcart_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_10])).

tff(c_343,plain,(
    k3_mcart_1('#skF_4','#skF_5','#skF_3') = k3_mcart_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_338])).

tff(c_362,plain,(
    ! [A_90,B_91,C_92] : k4_tarski(k4_tarski(A_90,B_91),C_92) = k3_mcart_1(A_90,B_91,C_92) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_407,plain,(
    ! [A_108,B_104,C_105,A_107,B_106] :
      ( k4_tarski(A_108,B_104) = A_107
      | k4_tarski(A_107,B_106) != k3_mcart_1(A_108,B_104,C_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_4])).

tff(c_414,plain,(
    ! [A_109,B_110] :
      ( k4_tarski('#skF_4','#skF_5') = A_109
      | k4_tarski(A_109,B_110) != k3_mcart_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_407])).

tff(c_417,plain,(
    ! [A_5,B_6,C_7] :
      ( k4_tarski(A_5,B_6) = k4_tarski('#skF_4','#skF_5')
      | k3_mcart_1(A_5,B_6,C_7) != k3_mcart_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_414])).

tff(c_466,plain,(
    k4_tarski('#skF_4','#skF_5') = k4_tarski('#skF_4','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_417])).

tff(c_494,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_5'
      | k4_tarski(A_1,B_2) != k4_tarski('#skF_4','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_2])).

tff(c_536,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_494])).

tff(c_538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:38:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.33  
% 2.03/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.33  %$ k3_mcart_1 > k4_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.36/1.33  
% 2.36/1.33  %Foreground sorts:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Background operators:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Foreground operators:
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.36/1.33  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.36/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.33  
% 2.36/1.34  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_mcart_1)).
% 2.36/1.34  tff(f_33, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.36/1.34  tff(f_31, axiom, (![A, B, C, D]: ((k4_tarski(A, B) = k4_tarski(C, D)) => ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_zfmisc_1)).
% 2.36/1.34  tff(c_8, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.34  tff(c_11, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_8])).
% 2.36/1.34  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_tarski(k4_tarski(A_5, B_6), C_7)=k3_mcart_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.34  tff(c_10, plain, (k3_mcart_1('#skF_1', '#skF_2', '#skF_3')=k3_mcart_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.34  tff(c_26, plain, (![A_16, B_17, C_18]: (k4_tarski(k4_tarski(A_16, B_17), C_18)=k3_mcart_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.34  tff(c_2, plain, (![D_4, B_2, C_3, A_1]: (D_4=B_2 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.34  tff(c_53, plain, (![C_23, A_20, B_21, A_22, B_19]: (C_23=B_21 | k4_tarski(A_22, B_21)!=k3_mcart_1(A_20, B_19, C_23))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2])).
% 2.36/1.34  tff(c_60, plain, (![B_24, A_25]: (B_24='#skF_3' | k4_tarski(A_25, B_24)!=k3_mcart_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 2.36/1.34  tff(c_63, plain, (![C_7, A_5, B_6]: (C_7='#skF_3' | k3_mcart_1(A_5, B_6, C_7)!=k3_mcart_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 2.36/1.34  tff(c_66, plain, ('#skF_6'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_63])).
% 2.36/1.34  tff(c_75, plain, (k3_mcart_1('#skF_1', '#skF_2', '#skF_3')=k3_mcart_1('#skF_4', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10])).
% 2.36/1.34  tff(c_4, plain, (![C_3, A_1, D_4, B_2]: (C_3=A_1 | k4_tarski(C_3, D_4)!=k4_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.34  tff(c_98, plain, (![C_39, D_36, A_37, B_35, C_38]: (k4_tarski(A_37, B_35)=C_38 | k4_tarski(C_38, D_36)!=k3_mcart_1(A_37, B_35, C_39))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 2.36/1.34  tff(c_105, plain, (![C_40, D_41]: (k4_tarski('#skF_1', '#skF_2')=C_40 | k4_tarski(C_40, D_41)!=k3_mcart_1('#skF_4', '#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_98])).
% 2.36/1.34  tff(c_108, plain, (![A_5, B_6, C_7]: (k4_tarski(A_5, B_6)=k4_tarski('#skF_1', '#skF_2') | k3_mcart_1(A_5, B_6, C_7)!=k3_mcart_1('#skF_4', '#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_105])).
% 2.36/1.34  tff(c_138, plain, (k4_tarski('#skF_1', '#skF_2')=k4_tarski('#skF_4', '#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_108])).
% 2.36/1.34  tff(c_160, plain, (![B_2, A_1]: (B_2='#skF_2' | k4_tarski(A_1, B_2)!=k4_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_2])).
% 2.36/1.34  tff(c_200, plain, ('#skF_5'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_160])).
% 2.36/1.34  tff(c_169, plain, (![C_3, D_4]: (C_3='#skF_1' | k4_tarski(C_3, D_4)!=k4_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_4])).
% 2.36/1.34  tff(c_254, plain, (![C_3, D_4]: (C_3='#skF_1' | k4_tarski(C_3, D_4)!=k4_tarski('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_169])).
% 2.36/1.34  tff(c_257, plain, ('#skF_1'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_254])).
% 2.36/1.34  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11, c_257])).
% 2.36/1.34  tff(c_260, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_8])).
% 2.36/1.34  tff(c_266, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_260])).
% 2.36/1.34  tff(c_261, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_8])).
% 2.36/1.34  tff(c_267, plain, (k3_mcart_1('#skF_4', '#skF_5', '#skF_6')=k3_mcart_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_10])).
% 2.36/1.34  tff(c_282, plain, (![A_66, B_67, C_68]: (k4_tarski(k4_tarski(A_66, B_67), C_68)=k3_mcart_1(A_66, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.34  tff(c_309, plain, (![B_70, C_73, B_72, A_71, A_69]: (C_73=B_70 | k4_tarski(A_71, B_70)!=k3_mcart_1(A_69, B_72, C_73))), inference(superposition, [status(thm), theory('equality')], [c_282, c_2])).
% 2.36/1.34  tff(c_316, plain, (![B_74, A_75]: (B_74='#skF_6' | k4_tarski(A_75, B_74)!=k3_mcart_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_267, c_309])).
% 2.36/1.34  tff(c_319, plain, (![C_7, A_5, B_6]: (C_7='#skF_6' | k3_mcart_1(A_5, B_6, C_7)!=k3_mcart_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_316])).
% 2.36/1.34  tff(c_333, plain, ('#skF_6'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_319])).
% 2.36/1.34  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_333])).
% 2.36/1.34  tff(c_336, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_260])).
% 2.36/1.34  tff(c_337, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_260])).
% 2.36/1.34  tff(c_338, plain, (k3_mcart_1('#skF_4', '#skF_5', '#skF_6')=k3_mcart_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_10])).
% 2.36/1.34  tff(c_343, plain, (k3_mcart_1('#skF_4', '#skF_5', '#skF_3')=k3_mcart_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_338])).
% 2.36/1.34  tff(c_362, plain, (![A_90, B_91, C_92]: (k4_tarski(k4_tarski(A_90, B_91), C_92)=k3_mcart_1(A_90, B_91, C_92))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.34  tff(c_407, plain, (![A_108, B_104, C_105, A_107, B_106]: (k4_tarski(A_108, B_104)=A_107 | k4_tarski(A_107, B_106)!=k3_mcart_1(A_108, B_104, C_105))), inference(superposition, [status(thm), theory('equality')], [c_362, c_4])).
% 2.36/1.34  tff(c_414, plain, (![A_109, B_110]: (k4_tarski('#skF_4', '#skF_5')=A_109 | k4_tarski(A_109, B_110)!=k3_mcart_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_343, c_407])).
% 2.36/1.34  tff(c_417, plain, (![A_5, B_6, C_7]: (k4_tarski(A_5, B_6)=k4_tarski('#skF_4', '#skF_5') | k3_mcart_1(A_5, B_6, C_7)!=k3_mcart_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_414])).
% 2.36/1.34  tff(c_466, plain, (k4_tarski('#skF_4', '#skF_5')=k4_tarski('#skF_4', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_417])).
% 2.36/1.34  tff(c_494, plain, (![B_2, A_1]: (B_2='#skF_5' | k4_tarski(A_1, B_2)!=k4_tarski('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_466, c_2])).
% 2.36/1.34  tff(c_536, plain, ('#skF_5'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_494])).
% 2.36/1.34  tff(c_538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_536])).
% 2.36/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.34  
% 2.36/1.34  Inference rules
% 2.36/1.34  ----------------------
% 2.36/1.34  #Ref     : 18
% 2.36/1.34  #Sup     : 128
% 2.36/1.34  #Fact    : 0
% 2.36/1.34  #Define  : 0
% 2.36/1.34  #Split   : 2
% 2.36/1.34  #Chain   : 0
% 2.36/1.34  #Close   : 0
% 2.36/1.34  
% 2.36/1.34  Ordering : KBO
% 2.36/1.34  
% 2.36/1.34  Simplification rules
% 2.36/1.34  ----------------------
% 2.36/1.34  #Subsume      : 45
% 2.36/1.34  #Demod        : 40
% 2.36/1.34  #Tautology    : 59
% 2.36/1.34  #SimpNegUnit  : 3
% 2.36/1.34  #BackRed      : 11
% 2.36/1.34  
% 2.36/1.34  #Partial instantiations: 0
% 2.36/1.34  #Strategies tried      : 1
% 2.36/1.34  
% 2.36/1.34  Timing (in seconds)
% 2.36/1.34  ----------------------
% 2.36/1.35  Preprocessing        : 0.27
% 2.36/1.35  Parsing              : 0.14
% 2.36/1.35  CNF conversion       : 0.02
% 2.36/1.35  Main loop            : 0.30
% 2.36/1.35  Inferencing          : 0.11
% 2.36/1.35  Reduction            : 0.08
% 2.36/1.35  Demodulation         : 0.06
% 2.36/1.35  BG Simplification    : 0.01
% 2.36/1.35  Subsumption          : 0.07
% 2.36/1.35  Abstraction          : 0.02
% 2.36/1.35  MUC search           : 0.00
% 2.36/1.35  Cooper               : 0.00
% 2.36/1.35  Total                : 0.60
% 2.36/1.35  Index Insertion      : 0.00
% 2.36/1.35  Index Deletion       : 0.00
% 2.36/1.35  Index Matching       : 0.00
% 2.36/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
