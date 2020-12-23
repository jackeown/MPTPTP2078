%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:41 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 107 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 ( 127 expanded)
%              Number of equality atoms :   38 ( 114 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_48,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_570,plain,(
    ! [A_71,B_72,C_73] : k2_xboole_0(k2_tarski(A_71,B_72),k1_tarski(C_73)) = k1_enumset1(A_71,B_72,C_73) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_579,plain,(
    ! [A_25,C_73] : k2_xboole_0(k1_tarski(A_25),k1_tarski(C_73)) = k1_enumset1(A_25,A_25,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_570])).

tff(c_582,plain,(
    ! [A_25,C_73] : k2_xboole_0(k1_tarski(A_25),k1_tarski(C_73)) = k2_tarski(A_25,C_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_579])).

tff(c_998,plain,(
    ! [A_94,C_95] : k2_xboole_0(k1_tarski(A_94),k1_tarski(C_95)) = k2_tarski(A_94,C_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_579])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_212,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k4_xboole_0(B_51,A_50)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_225,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_212])).

tff(c_232,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_225])).

tff(c_1004,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_232])).

tff(c_40,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_tarski(A_22,B_23),k1_tarski(C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1016,plain,(
    ! [C_24] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(C_24)) = k1_enumset1('#skF_4','#skF_3',C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_1004,c_40])).

tff(c_1029,plain,(
    ! [C_96] : k1_enumset1('#skF_4','#skF_3',C_96) = k2_tarski('#skF_4',C_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_1016])).

tff(c_18,plain,(
    ! [E_18,A_12,C_14] : r2_hidden(E_18,k1_enumset1(A_12,E_18,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1051,plain,(
    ! [C_96] : r2_hidden('#skF_3',k2_tarski('#skF_4',C_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_18])).

tff(c_740,plain,(
    ! [E_78,C_79,B_80,A_81] :
      ( E_78 = C_79
      | E_78 = B_80
      | E_78 = A_81
      | ~ r2_hidden(E_78,k1_enumset1(A_81,B_80,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7870,plain,(
    ! [E_213,B_214,A_215] :
      ( E_213 = B_214
      | E_213 = A_215
      | E_213 = A_215
      | ~ r2_hidden(E_213,k2_tarski(A_215,B_214)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_740])).

tff(c_7881,plain,(
    ! [C_96] :
      ( C_96 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1051,c_7870])).

tff(c_7907,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_7881])).

tff(c_7901,plain,(
    ! [C_96] : C_96 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_7881])).

tff(c_8313,plain,(
    ! [C_2490] : C_2490 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7907,c_7901])).

tff(c_8691,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8313,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:42:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/2.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.77  
% 7.31/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.77  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.31/2.77  
% 7.31/2.77  %Foreground sorts:
% 7.31/2.77  
% 7.31/2.77  
% 7.31/2.77  %Background operators:
% 7.31/2.77  
% 7.31/2.77  
% 7.31/2.77  %Foreground operators:
% 7.31/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.31/2.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.31/2.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.31/2.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.31/2.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.31/2.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.31/2.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.31/2.77  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.77  tff('#skF_4', type, '#skF_4': $i).
% 7.31/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.31/2.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.31/2.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.31/2.77  
% 7.31/2.79  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 7.31/2.79  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.31/2.79  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.31/2.79  tff(f_56, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 7.31/2.79  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.31/2.79  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.31/2.79  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.31/2.79  tff(c_48, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.31/2.79  tff(c_44, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.31/2.79  tff(c_42, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.31/2.79  tff(c_570, plain, (![A_71, B_72, C_73]: (k2_xboole_0(k2_tarski(A_71, B_72), k1_tarski(C_73))=k1_enumset1(A_71, B_72, C_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.31/2.79  tff(c_579, plain, (![A_25, C_73]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(C_73))=k1_enumset1(A_25, A_25, C_73))), inference(superposition, [status(thm), theory('equality')], [c_42, c_570])).
% 7.31/2.79  tff(c_582, plain, (![A_25, C_73]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(C_73))=k2_tarski(A_25, C_73))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_579])).
% 7.31/2.79  tff(c_998, plain, (![A_94, C_95]: (k2_xboole_0(k1_tarski(A_94), k1_tarski(C_95))=k2_tarski(A_94, C_95))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_579])).
% 7.31/2.79  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.31/2.79  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.31/2.79  tff(c_212, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k4_xboole_0(B_51, A_50))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.31/2.79  tff(c_225, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_212])).
% 7.31/2.79  tff(c_232, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_225])).
% 7.31/2.79  tff(c_1004, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_998, c_232])).
% 7.31/2.79  tff(c_40, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k2_tarski(A_22, B_23), k1_tarski(C_24))=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.31/2.79  tff(c_1016, plain, (![C_24]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(C_24))=k1_enumset1('#skF_4', '#skF_3', C_24))), inference(superposition, [status(thm), theory('equality')], [c_1004, c_40])).
% 7.31/2.79  tff(c_1029, plain, (![C_96]: (k1_enumset1('#skF_4', '#skF_3', C_96)=k2_tarski('#skF_4', C_96))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_1016])).
% 7.31/2.79  tff(c_18, plain, (![E_18, A_12, C_14]: (r2_hidden(E_18, k1_enumset1(A_12, E_18, C_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.31/2.79  tff(c_1051, plain, (![C_96]: (r2_hidden('#skF_3', k2_tarski('#skF_4', C_96)))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_18])).
% 7.31/2.79  tff(c_740, plain, (![E_78, C_79, B_80, A_81]: (E_78=C_79 | E_78=B_80 | E_78=A_81 | ~r2_hidden(E_78, k1_enumset1(A_81, B_80, C_79)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.31/2.79  tff(c_7870, plain, (![E_213, B_214, A_215]: (E_213=B_214 | E_213=A_215 | E_213=A_215 | ~r2_hidden(E_213, k2_tarski(A_215, B_214)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_740])).
% 7.31/2.79  tff(c_7881, plain, (![C_96]: (C_96='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_1051, c_7870])).
% 7.31/2.79  tff(c_7907, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_7881])).
% 7.31/2.79  tff(c_7901, plain, (![C_96]: (C_96='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_7881])).
% 7.31/2.79  tff(c_8313, plain, (![C_2490]: (C_2490='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7907, c_7901])).
% 7.31/2.79  tff(c_8691, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8313, c_48])).
% 7.31/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.79  
% 7.31/2.79  Inference rules
% 7.31/2.79  ----------------------
% 7.31/2.79  #Ref     : 0
% 7.31/2.79  #Sup     : 2364
% 7.31/2.79  #Fact    : 5
% 7.31/2.79  #Define  : 0
% 7.31/2.79  #Split   : 0
% 7.31/2.79  #Chain   : 0
% 7.31/2.79  #Close   : 0
% 7.31/2.79  
% 7.31/2.79  Ordering : KBO
% 7.31/2.79  
% 7.31/2.79  Simplification rules
% 7.31/2.79  ----------------------
% 7.31/2.79  #Subsume      : 277
% 7.31/2.79  #Demod        : 1632
% 7.31/2.79  #Tautology    : 944
% 7.31/2.79  #SimpNegUnit  : 18
% 7.31/2.79  #BackRed      : 0
% 7.31/2.79  
% 7.31/2.79  #Partial instantiations: 87
% 7.31/2.79  #Strategies tried      : 1
% 7.31/2.79  
% 7.31/2.79  Timing (in seconds)
% 7.31/2.79  ----------------------
% 7.31/2.79  Preprocessing        : 0.30
% 7.31/2.79  Parsing              : 0.15
% 7.31/2.79  CNF conversion       : 0.02
% 7.31/2.79  Main loop            : 1.71
% 7.31/2.79  Inferencing          : 0.46
% 7.31/2.79  Reduction            : 0.89
% 7.31/2.79  Demodulation         : 0.79
% 7.31/2.79  BG Simplification    : 0.06
% 7.31/2.79  Subsumption          : 0.24
% 7.31/2.79  Abstraction          : 0.08
% 7.31/2.79  MUC search           : 0.00
% 7.31/2.79  Cooper               : 0.00
% 7.31/2.79  Total                : 2.05
% 7.31/2.79  Index Insertion      : 0.00
% 7.31/2.79  Index Deletion       : 0.00
% 7.31/2.79  Index Matching       : 0.00
% 7.31/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
