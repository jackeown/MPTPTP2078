%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:36 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 166 expanded)
%              Number of leaves         :   33 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :   59 ( 185 expanded)
%              Number of equality atoms :   49 ( 159 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

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

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_308,plain,(
    ! [A_88,B_89,C_90,D_91] : k2_xboole_0(k1_enumset1(A_88,B_89,C_90),k1_tarski(D_91)) = k2_enumset1(A_88,B_89,C_90,D_91) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_326,plain,(
    ! [A_24,B_25,D_91] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(D_91)) = k2_enumset1(A_24,A_24,B_25,D_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_308])).

tff(c_330,plain,(
    ! [A_92,B_93,D_94] : k2_xboole_0(k2_tarski(A_92,B_93),k1_tarski(D_94)) = k1_enumset1(A_92,B_93,D_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_326])).

tff(c_339,plain,(
    ! [A_23,D_94] : k2_xboole_0(k1_tarski(A_23),k1_tarski(D_94)) = k1_enumset1(A_23,A_23,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_330])).

tff(c_342,plain,(
    ! [A_23,D_94] : k2_xboole_0(k1_tarski(A_23),k1_tarski(D_94)) = k2_tarski(A_23,D_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_339])).

tff(c_343,plain,(
    ! [A_95,D_96] : k2_xboole_0(k1_tarski(A_95),k1_tarski(D_96)) = k2_tarski(A_95,D_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_339])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_142,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_142])).

tff(c_154,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_10])).

tff(c_161,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_349,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_161])).

tff(c_329,plain,(
    ! [A_24,B_25,D_91] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(D_91)) = k1_enumset1(A_24,B_25,D_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_326])).

tff(c_361,plain,(
    ! [D_91] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_91)) = k1_enumset1('#skF_4','#skF_3',D_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_329])).

tff(c_374,plain,(
    ! [D_97] : k1_enumset1('#skF_4','#skF_3',D_97) = k2_tarski('#skF_4',D_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_361])).

tff(c_16,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_393,plain,(
    ! [D_97] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_16])).

tff(c_447,plain,(
    ! [E_99,C_100,B_101,A_102] :
      ( E_99 = C_100
      | E_99 = B_101
      | E_99 = A_102
      | ~ r2_hidden(E_99,k1_enumset1(A_102,B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_815,plain,(
    ! [E_123,B_124,A_125] :
      ( E_123 = B_124
      | E_123 = A_125
      | E_123 = A_125
      | ~ r2_hidden(E_123,k2_tarski(A_125,B_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_447])).

tff(c_818,plain,(
    ! [D_97] :
      ( D_97 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_393,c_815])).

tff(c_851,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_818])).

tff(c_836,plain,(
    ! [D_97] : D_97 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_818])).

tff(c_1029,plain,(
    ! [D_2434] : D_2434 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_836])).

tff(c_1189,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.51  
% 3.39/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.52  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.39/1.52  
% 3.39/1.52  %Foreground sorts:
% 3.39/1.52  
% 3.39/1.52  
% 3.39/1.52  %Background operators:
% 3.39/1.52  
% 3.39/1.52  
% 3.39/1.52  %Foreground operators:
% 3.39/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.39/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.39/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.39/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.39/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.39/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.39/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.39/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.39/1.52  
% 3.39/1.53  tff(f_75, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.39/1.53  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.39/1.53  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.39/1.53  tff(f_62, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.39/1.53  tff(f_56, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.39/1.53  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.39/1.53  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.39/1.53  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.39/1.53  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.39/1.53  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.39/1.53  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.39/1.53  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.39/1.53  tff(c_42, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.39/1.53  tff(c_40, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.53  tff(c_44, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.39/1.53  tff(c_308, plain, (![A_88, B_89, C_90, D_91]: (k2_xboole_0(k1_enumset1(A_88, B_89, C_90), k1_tarski(D_91))=k2_enumset1(A_88, B_89, C_90, D_91))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.39/1.53  tff(c_326, plain, (![A_24, B_25, D_91]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(D_91))=k2_enumset1(A_24, A_24, B_25, D_91))), inference(superposition, [status(thm), theory('equality')], [c_42, c_308])).
% 3.39/1.53  tff(c_330, plain, (![A_92, B_93, D_94]: (k2_xboole_0(k2_tarski(A_92, B_93), k1_tarski(D_94))=k1_enumset1(A_92, B_93, D_94))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_326])).
% 3.39/1.53  tff(c_339, plain, (![A_23, D_94]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(D_94))=k1_enumset1(A_23, A_23, D_94))), inference(superposition, [status(thm), theory('equality')], [c_40, c_330])).
% 3.39/1.53  tff(c_342, plain, (![A_23, D_94]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(D_94))=k2_tarski(A_23, D_94))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_339])).
% 3.39/1.53  tff(c_343, plain, (![A_95, D_96]: (k2_xboole_0(k1_tarski(A_95), k1_tarski(D_96))=k2_tarski(A_95, D_96))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_339])).
% 3.39/1.53  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.53  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.53  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.39/1.53  tff(c_95, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.53  tff(c_99, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_56, c_95])).
% 3.39/1.53  tff(c_142, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.53  tff(c_151, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_142])).
% 3.39/1.53  tff(c_154, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_151])).
% 3.39/1.53  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.53  tff(c_158, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154, c_10])).
% 3.39/1.53  tff(c_161, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_158])).
% 3.39/1.53  tff(c_349, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_343, c_161])).
% 3.39/1.53  tff(c_329, plain, (![A_24, B_25, D_91]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(D_91))=k1_enumset1(A_24, B_25, D_91))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_326])).
% 3.39/1.53  tff(c_361, plain, (![D_91]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_91))=k1_enumset1('#skF_4', '#skF_3', D_91))), inference(superposition, [status(thm), theory('equality')], [c_349, c_329])).
% 3.39/1.53  tff(c_374, plain, (![D_97]: (k1_enumset1('#skF_4', '#skF_3', D_97)=k2_tarski('#skF_4', D_97))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_361])).
% 3.39/1.53  tff(c_16, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.39/1.53  tff(c_393, plain, (![D_97]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_97)))), inference(superposition, [status(thm), theory('equality')], [c_374, c_16])).
% 3.39/1.53  tff(c_447, plain, (![E_99, C_100, B_101, A_102]: (E_99=C_100 | E_99=B_101 | E_99=A_102 | ~r2_hidden(E_99, k1_enumset1(A_102, B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.39/1.53  tff(c_815, plain, (![E_123, B_124, A_125]: (E_123=B_124 | E_123=A_125 | E_123=A_125 | ~r2_hidden(E_123, k2_tarski(A_125, B_124)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_447])).
% 3.39/1.53  tff(c_818, plain, (![D_97]: (D_97='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_393, c_815])).
% 3.39/1.53  tff(c_851, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_818])).
% 3.39/1.53  tff(c_836, plain, (![D_97]: (D_97='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_818])).
% 3.39/1.53  tff(c_1029, plain, (![D_2434]: (D_2434='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_851, c_836])).
% 3.39/1.53  tff(c_1189, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1029, c_54])).
% 3.39/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.53  
% 3.39/1.53  Inference rules
% 3.39/1.53  ----------------------
% 3.39/1.53  #Ref     : 0
% 3.39/1.53  #Sup     : 333
% 3.39/1.53  #Fact    : 0
% 3.39/1.53  #Define  : 0
% 3.39/1.53  #Split   : 0
% 3.39/1.53  #Chain   : 0
% 3.39/1.53  #Close   : 0
% 3.39/1.53  
% 3.39/1.53  Ordering : KBO
% 3.39/1.53  
% 3.39/1.53  Simplification rules
% 3.39/1.53  ----------------------
% 3.39/1.53  #Subsume      : 64
% 3.39/1.53  #Demod        : 122
% 3.39/1.53  #Tautology    : 166
% 3.39/1.53  #SimpNegUnit  : 7
% 3.39/1.53  #BackRed      : 0
% 3.39/1.53  
% 3.39/1.53  #Partial instantiations: 44
% 3.39/1.53  #Strategies tried      : 1
% 3.39/1.53  
% 3.39/1.53  Timing (in seconds)
% 3.39/1.53  ----------------------
% 3.51/1.53  Preprocessing        : 0.32
% 3.51/1.53  Parsing              : 0.16
% 3.51/1.53  CNF conversion       : 0.02
% 3.51/1.53  Main loop            : 0.44
% 3.51/1.53  Inferencing          : 0.18
% 3.51/1.53  Reduction            : 0.15
% 3.51/1.53  Demodulation         : 0.12
% 3.51/1.53  BG Simplification    : 0.02
% 3.51/1.53  Subsumption          : 0.06
% 3.51/1.53  Abstraction          : 0.02
% 3.51/1.53  MUC search           : 0.00
% 3.51/1.53  Cooper               : 0.00
% 3.51/1.53  Total                : 0.80
% 3.51/1.53  Index Insertion      : 0.00
% 3.51/1.53  Index Deletion       : 0.00
% 3.51/1.53  Index Matching       : 0.00
% 3.51/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
