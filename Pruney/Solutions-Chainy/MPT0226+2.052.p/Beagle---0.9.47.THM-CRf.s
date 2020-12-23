%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:44 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 108 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 ( 127 expanded)
%              Number of equality atoms :   38 ( 114 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_33,axiom,(
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

tff(c_42,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_338,plain,(
    ! [A_65,B_66,C_67] : k2_xboole_0(k2_tarski(A_65,B_66),k1_tarski(C_67)) = k1_enumset1(A_65,B_66,C_67) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_347,plain,(
    ! [A_20,C_67] : k2_xboole_0(k1_tarski(A_20),k1_tarski(C_67)) = k1_enumset1(A_20,A_20,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_338])).

tff(c_350,plain,(
    ! [A_20,C_67] : k2_xboole_0(k1_tarski(A_20),k1_tarski(C_67)) = k2_tarski(A_20,C_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_347])).

tff(c_351,plain,(
    ! [A_68,C_69] : k2_xboole_0(k1_tarski(A_68),k1_tarski(C_69)) = k2_tarski(A_68,C_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_347])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_129,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k4_xboole_0(B_51,A_50)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_138,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_129])).

tff(c_141,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_361,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_141])).

tff(c_38,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(C_19)) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_379,plain,(
    ! [C_19] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(C_19)) = k1_enumset1('#skF_4','#skF_3',C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_38])).

tff(c_392,plain,(
    ! [C_70] : k1_enumset1('#skF_4','#skF_3',C_70) = k2_tarski('#skF_4',C_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_379])).

tff(c_18,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_398,plain,(
    ! [C_70] : r2_hidden('#skF_3',k2_tarski('#skF_4',C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_18])).

tff(c_458,plain,(
    ! [E_78,C_79,B_80,A_81] :
      ( E_78 = C_79
      | E_78 = B_80
      | E_78 = A_81
      | ~ r2_hidden(E_78,k1_enumset1(A_81,B_80,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_480,plain,(
    ! [E_82,B_83,A_84] :
      ( E_82 = B_83
      | E_82 = A_84
      | E_82 = A_84
      | ~ r2_hidden(E_82,k2_tarski(A_84,B_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_458])).

tff(c_483,plain,(
    ! [C_70] :
      ( C_70 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_398,c_480])).

tff(c_504,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_483])).

tff(c_498,plain,(
    ! [C_70] : C_70 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_483])).

tff(c_650,plain,(
    ! [C_1275] : C_1275 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_498])).

tff(c_787,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.86/1.39  
% 2.86/1.39  %Foreground sorts:
% 2.86/1.39  
% 2.86/1.39  
% 2.86/1.39  %Background operators:
% 2.86/1.39  
% 2.86/1.39  
% 2.86/1.39  %Foreground operators:
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.86/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.86/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.86/1.39  
% 2.86/1.40  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.86/1.40  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.86/1.40  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.86/1.40  tff(f_54, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.86/1.40  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.86/1.40  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.86/1.40  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.86/1.40  tff(c_48, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.86/1.40  tff(c_42, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.40  tff(c_40, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.40  tff(c_338, plain, (![A_65, B_66, C_67]: (k2_xboole_0(k2_tarski(A_65, B_66), k1_tarski(C_67))=k1_enumset1(A_65, B_66, C_67))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.86/1.40  tff(c_347, plain, (![A_20, C_67]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(C_67))=k1_enumset1(A_20, A_20, C_67))), inference(superposition, [status(thm), theory('equality')], [c_40, c_338])).
% 2.86/1.40  tff(c_350, plain, (![A_20, C_67]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(C_67))=k2_tarski(A_20, C_67))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_347])).
% 2.86/1.40  tff(c_351, plain, (![A_68, C_69]: (k2_xboole_0(k1_tarski(A_68), k1_tarski(C_69))=k2_tarski(A_68, C_69))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_347])).
% 2.86/1.40  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.40  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.86/1.40  tff(c_129, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k4_xboole_0(B_51, A_50))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.40  tff(c_138, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_129])).
% 2.86/1.40  tff(c_141, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_138])).
% 2.86/1.40  tff(c_361, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_351, c_141])).
% 2.86/1.40  tff(c_38, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(C_19))=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.86/1.40  tff(c_379, plain, (![C_19]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(C_19))=k1_enumset1('#skF_4', '#skF_3', C_19))), inference(superposition, [status(thm), theory('equality')], [c_361, c_38])).
% 2.86/1.40  tff(c_392, plain, (![C_70]: (k1_enumset1('#skF_4', '#skF_3', C_70)=k2_tarski('#skF_4', C_70))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_379])).
% 2.86/1.40  tff(c_18, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.40  tff(c_398, plain, (![C_70]: (r2_hidden('#skF_3', k2_tarski('#skF_4', C_70)))), inference(superposition, [status(thm), theory('equality')], [c_392, c_18])).
% 2.86/1.40  tff(c_458, plain, (![E_78, C_79, B_80, A_81]: (E_78=C_79 | E_78=B_80 | E_78=A_81 | ~r2_hidden(E_78, k1_enumset1(A_81, B_80, C_79)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.40  tff(c_480, plain, (![E_82, B_83, A_84]: (E_82=B_83 | E_82=A_84 | E_82=A_84 | ~r2_hidden(E_82, k2_tarski(A_84, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_458])).
% 2.86/1.40  tff(c_483, plain, (![C_70]: (C_70='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_398, c_480])).
% 2.86/1.40  tff(c_504, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_483])).
% 2.86/1.40  tff(c_498, plain, (![C_70]: (C_70='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_483])).
% 2.86/1.40  tff(c_650, plain, (![C_1275]: (C_1275='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_504, c_498])).
% 2.86/1.40  tff(c_787, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_650, c_48])).
% 2.86/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  Inference rules
% 2.86/1.40  ----------------------
% 2.86/1.40  #Ref     : 0
% 2.86/1.40  #Sup     : 238
% 2.86/1.40  #Fact    : 0
% 2.86/1.40  #Define  : 0
% 2.86/1.40  #Split   : 0
% 2.86/1.40  #Chain   : 0
% 2.86/1.40  #Close   : 0
% 2.86/1.40  
% 2.86/1.40  Ordering : KBO
% 2.86/1.40  
% 2.86/1.40  Simplification rules
% 2.86/1.40  ----------------------
% 2.86/1.40  #Subsume      : 49
% 2.86/1.40  #Demod        : 57
% 2.86/1.40  #Tautology    : 96
% 2.86/1.40  #SimpNegUnit  : 1
% 2.86/1.40  #BackRed      : 0
% 2.86/1.40  
% 2.86/1.40  #Partial instantiations: 38
% 2.86/1.40  #Strategies tried      : 1
% 2.86/1.40  
% 2.86/1.40  Timing (in seconds)
% 2.86/1.40  ----------------------
% 2.86/1.41  Preprocessing        : 0.31
% 2.86/1.41  Parsing              : 0.16
% 2.86/1.41  CNF conversion       : 0.02
% 2.86/1.41  Main loop            : 0.34
% 2.86/1.41  Inferencing          : 0.15
% 2.86/1.41  Reduction            : 0.11
% 2.86/1.41  Demodulation         : 0.08
% 2.86/1.41  BG Simplification    : 0.02
% 2.86/1.41  Subsumption          : 0.05
% 2.86/1.41  Abstraction          : 0.02
% 2.86/1.41  MUC search           : 0.00
% 2.86/1.41  Cooper               : 0.00
% 2.86/1.41  Total                : 0.69
% 2.86/1.41  Index Insertion      : 0.00
% 2.86/1.41  Index Deletion       : 0.00
% 2.86/1.41  Index Matching       : 0.00
% 2.86/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
