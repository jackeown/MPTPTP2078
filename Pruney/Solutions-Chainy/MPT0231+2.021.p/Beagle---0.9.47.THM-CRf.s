%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:17 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   60 (  83 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  84 expanded)
%              Number of equality atoms :   44 (  70 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_70,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_56,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_605,plain,(
    ! [A_87,B_88,C_89] : k2_xboole_0(k1_tarski(A_87),k2_tarski(B_88,C_89)) = k1_enumset1(A_87,B_88,C_89) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_453,plain,(
    ! [A_79,B_80] : k5_xboole_0(k5_xboole_0(A_79,B_80),k3_xboole_0(A_79,B_80)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_474,plain,(
    ! [A_5] : k5_xboole_0(k5_xboole_0(A_5,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_453])).

tff(c_480,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_474])).

tff(c_58,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_207,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_215,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_207])).

tff(c_277,plain,(
    ! [A_72,B_73] : k2_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_286,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_3','#skF_4')) = k2_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_277])).

tff(c_482,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_286])).

tff(c_611,plain,(
    k1_enumset1('#skF_5','#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_482])).

tff(c_30,plain,(
    ! [E_24,A_18,C_20] : r2_hidden(E_24,k1_enumset1(A_18,E_24,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_632,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_30])).

tff(c_52,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1235,plain,(
    ! [A_117,A_118] : k2_xboole_0(k1_tarski(A_117),k1_tarski(A_118)) = k1_enumset1(A_117,A_118,A_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_605])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_301,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k4_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_353,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_301])).

tff(c_363,plain,(
    ! [A_76] : k4_xboole_0(A_76,A_76) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_353])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_371,plain,(
    ! [A_76] : k2_xboole_0(A_76,k1_xboole_0) = k2_xboole_0(A_76,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_10])).

tff(c_499,plain,(
    ! [A_76] : k2_xboole_0(A_76,A_76) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_371])).

tff(c_1283,plain,(
    ! [A_123] : k1_enumset1(A_123,A_123,A_123) = k1_tarski(A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_499])).

tff(c_26,plain,(
    ! [E_24,C_20,B_19,A_18] :
      ( E_24 = C_20
      | E_24 = B_19
      | E_24 = A_18
      | ~ r2_hidden(E_24,k1_enumset1(A_18,B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2072,plain,(
    ! [E_152,A_153] :
      ( E_152 = A_153
      | E_152 = A_153
      | E_152 = A_153
      | ~ r2_hidden(E_152,k1_tarski(A_153)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1283,c_26])).

tff(c_2079,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_632,c_2072])).

tff(c_2090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_2079])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.55  
% 3.30/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.30/1.55  
% 3.30/1.55  %Foreground sorts:
% 3.30/1.55  
% 3.30/1.55  
% 3.30/1.55  %Background operators:
% 3.30/1.55  
% 3.30/1.55  
% 3.30/1.55  %Foreground operators:
% 3.30/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.30/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.30/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.30/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.30/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.30/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.30/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.30/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.30/1.55  
% 3.30/1.56  tff(f_77, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 3.30/1.56  tff(f_68, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.30/1.56  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.30/1.56  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.30/1.56  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.30/1.56  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.30/1.56  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.30/1.56  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.30/1.56  tff(f_70, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.30/1.56  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.30/1.56  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.30/1.56  tff(c_56, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.56  tff(c_605, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k1_tarski(A_87), k2_tarski(B_88, C_89))=k1_enumset1(A_87, B_88, C_89))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.30/1.56  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.56  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.30/1.56  tff(c_453, plain, (![A_79, B_80]: (k5_xboole_0(k5_xboole_0(A_79, B_80), k3_xboole_0(A_79, B_80))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.56  tff(c_474, plain, (![A_5]: (k5_xboole_0(k5_xboole_0(A_5, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_453])).
% 3.30/1.56  tff(c_480, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_474])).
% 3.30/1.56  tff(c_58, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.30/1.56  tff(c_207, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.30/1.56  tff(c_215, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_207])).
% 3.30/1.56  tff(c_277, plain, (![A_72, B_73]: (k2_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.56  tff(c_286, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_3', '#skF_4'))=k2_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_215, c_277])).
% 3.30/1.56  tff(c_482, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_286])).
% 3.30/1.56  tff(c_611, plain, (k1_enumset1('#skF_5', '#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_605, c_482])).
% 3.30/1.56  tff(c_30, plain, (![E_24, A_18, C_20]: (r2_hidden(E_24, k1_enumset1(A_18, E_24, C_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.30/1.56  tff(c_632, plain, (r2_hidden('#skF_3', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_611, c_30])).
% 3.30/1.56  tff(c_52, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.30/1.56  tff(c_1235, plain, (![A_117, A_118]: (k2_xboole_0(k1_tarski(A_117), k1_tarski(A_118))=k1_enumset1(A_117, A_118, A_118))), inference(superposition, [status(thm), theory('equality')], [c_52, c_605])).
% 3.30/1.56  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.56  tff(c_301, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k4_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.30/1.56  tff(c_353, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_301])).
% 3.30/1.56  tff(c_363, plain, (![A_76]: (k4_xboole_0(A_76, A_76)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_353])).
% 3.30/1.56  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.56  tff(c_371, plain, (![A_76]: (k2_xboole_0(A_76, k1_xboole_0)=k2_xboole_0(A_76, A_76))), inference(superposition, [status(thm), theory('equality')], [c_363, c_10])).
% 3.30/1.56  tff(c_499, plain, (![A_76]: (k2_xboole_0(A_76, A_76)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_480, c_371])).
% 3.30/1.56  tff(c_1283, plain, (![A_123]: (k1_enumset1(A_123, A_123, A_123)=k1_tarski(A_123))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_499])).
% 3.30/1.56  tff(c_26, plain, (![E_24, C_20, B_19, A_18]: (E_24=C_20 | E_24=B_19 | E_24=A_18 | ~r2_hidden(E_24, k1_enumset1(A_18, B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.30/1.56  tff(c_2072, plain, (![E_152, A_153]: (E_152=A_153 | E_152=A_153 | E_152=A_153 | ~r2_hidden(E_152, k1_tarski(A_153)))), inference(superposition, [status(thm), theory('equality')], [c_1283, c_26])).
% 3.30/1.56  tff(c_2079, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_632, c_2072])).
% 3.30/1.56  tff(c_2090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_2079])).
% 3.30/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.56  
% 3.30/1.56  Inference rules
% 3.30/1.56  ----------------------
% 3.30/1.56  #Ref     : 0
% 3.30/1.56  #Sup     : 503
% 3.30/1.56  #Fact    : 0
% 3.30/1.56  #Define  : 0
% 3.30/1.56  #Split   : 1
% 3.30/1.56  #Chain   : 0
% 3.30/1.56  #Close   : 0
% 3.30/1.56  
% 3.30/1.56  Ordering : KBO
% 3.30/1.56  
% 3.30/1.56  Simplification rules
% 3.30/1.56  ----------------------
% 3.30/1.56  #Subsume      : 1
% 3.30/1.56  #Demod        : 499
% 3.30/1.56  #Tautology    : 409
% 3.30/1.56  #SimpNegUnit  : 3
% 3.30/1.56  #BackRed      : 4
% 3.30/1.56  
% 3.30/1.56  #Partial instantiations: 0
% 3.30/1.56  #Strategies tried      : 1
% 3.30/1.56  
% 3.30/1.56  Timing (in seconds)
% 3.30/1.56  ----------------------
% 3.30/1.57  Preprocessing        : 0.31
% 3.30/1.57  Parsing              : 0.15
% 3.30/1.57  CNF conversion       : 0.02
% 3.30/1.57  Main loop            : 0.49
% 3.30/1.57  Inferencing          : 0.16
% 3.30/1.57  Reduction            : 0.19
% 3.30/1.57  Demodulation         : 0.15
% 3.30/1.57  BG Simplification    : 0.02
% 3.30/1.57  Subsumption          : 0.08
% 3.30/1.57  Abstraction          : 0.03
% 3.30/1.57  MUC search           : 0.00
% 3.30/1.57  Cooper               : 0.00
% 3.30/1.57  Total                : 0.83
% 3.30/1.57  Index Insertion      : 0.00
% 3.30/1.57  Index Deletion       : 0.00
% 3.30/1.57  Index Matching       : 0.00
% 3.30/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
