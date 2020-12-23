%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:53 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_54,axiom,(
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
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_286,plain,(
    ! [A_86,B_87,C_88,D_89] : k2_xboole_0(k1_enumset1(A_86,B_87,C_88),k1_tarski(D_89)) = k2_enumset1(A_86,B_87,C_88,D_89) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_301,plain,(
    ! [A_23,B_24,D_89] : k2_xboole_0(k2_tarski(A_23,B_24),k1_tarski(D_89)) = k2_enumset1(A_23,A_23,B_24,D_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_286])).

tff(c_330,plain,(
    ! [A_94,B_95,D_96] : k2_xboole_0(k2_tarski(A_94,B_95),k1_tarski(D_96)) = k1_enumset1(A_94,B_95,D_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_301])).

tff(c_351,plain,(
    ! [A_22,D_96] : k2_xboole_0(k1_tarski(A_22),k1_tarski(D_96)) = k1_enumset1(A_22,A_22,D_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_330])).

tff(c_354,plain,(
    ! [A_22,D_96] : k2_xboole_0(k1_tarski(A_22),k1_tarski(D_96)) = k2_tarski(A_22,D_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_351])).

tff(c_355,plain,(
    ! [A_97,D_98] : k2_xboole_0(k1_tarski(A_97),k1_tarski(D_98)) = k2_tarski(A_97,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_351])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_172,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_172])).

tff(c_243,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_252,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_243])).

tff(c_255,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_252])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_259,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k2_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_10])).

tff(c_262,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_259])).

tff(c_361,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_262])).

tff(c_310,plain,(
    ! [A_23,B_24,D_89] : k2_xboole_0(k2_tarski(A_23,B_24),k1_tarski(D_89)) = k1_enumset1(A_23,B_24,D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_301])).

tff(c_385,plain,(
    ! [D_89] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_89)) = k1_enumset1('#skF_4','#skF_3',D_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_310])).

tff(c_407,plain,(
    ! [D_104] : k1_enumset1('#skF_4','#skF_3',D_104) = k2_tarski('#skF_4',D_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_385])).

tff(c_18,plain,(
    ! [E_17,A_11,C_13] : r2_hidden(E_17,k1_enumset1(A_11,E_17,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_422,plain,(
    ! [D_104] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_18])).

tff(c_311,plain,(
    ! [E_90,C_91,B_92,A_93] :
      ( E_90 = C_91
      | E_90 = B_92
      | E_90 = A_93
      | ~ r2_hidden(E_90,k1_enumset1(A_93,B_92,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_978,plain,(
    ! [E_149,B_150,A_151] :
      ( E_149 = B_150
      | E_149 = A_151
      | E_149 = A_151
      | ~ r2_hidden(E_149,k2_tarski(A_151,B_150)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_311])).

tff(c_993,plain,(
    ! [D_104] :
      ( D_104 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_422,c_978])).

tff(c_1017,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_993])).

tff(c_1011,plain,(
    ! [D_104] : D_104 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_993])).

tff(c_1224,plain,(
    ! [D_2822] : D_2822 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_1011])).

tff(c_1415,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.59  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.32/1.59  
% 3.32/1.59  %Foreground sorts:
% 3.32/1.59  
% 3.32/1.59  
% 3.32/1.59  %Background operators:
% 3.32/1.59  
% 3.32/1.59  
% 3.32/1.59  %Foreground operators:
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.32/1.59  
% 3.32/1.60  tff(f_75, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 3.32/1.60  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.32/1.60  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.32/1.60  tff(f_62, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.32/1.60  tff(f_56, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.32/1.60  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.32/1.60  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.32/1.60  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.32/1.60  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.32/1.60  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.32/1.60  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.32/1.60  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.60  tff(c_42, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.32/1.60  tff(c_40, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.32/1.60  tff(c_44, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.32/1.60  tff(c_286, plain, (![A_86, B_87, C_88, D_89]: (k2_xboole_0(k1_enumset1(A_86, B_87, C_88), k1_tarski(D_89))=k2_enumset1(A_86, B_87, C_88, D_89))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.32/1.60  tff(c_301, plain, (![A_23, B_24, D_89]: (k2_xboole_0(k2_tarski(A_23, B_24), k1_tarski(D_89))=k2_enumset1(A_23, A_23, B_24, D_89))), inference(superposition, [status(thm), theory('equality')], [c_42, c_286])).
% 3.32/1.60  tff(c_330, plain, (![A_94, B_95, D_96]: (k2_xboole_0(k2_tarski(A_94, B_95), k1_tarski(D_96))=k1_enumset1(A_94, B_95, D_96))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_301])).
% 3.32/1.60  tff(c_351, plain, (![A_22, D_96]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(D_96))=k1_enumset1(A_22, A_22, D_96))), inference(superposition, [status(thm), theory('equality')], [c_40, c_330])).
% 3.32/1.60  tff(c_354, plain, (![A_22, D_96]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(D_96))=k2_tarski(A_22, D_96))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_351])).
% 3.32/1.60  tff(c_355, plain, (![A_97, D_98]: (k2_xboole_0(k1_tarski(A_97), k1_tarski(D_98))=k2_tarski(A_97, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_351])).
% 3.32/1.60  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.60  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.60  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.60  tff(c_172, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.60  tff(c_176, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_56, c_172])).
% 3.32/1.60  tff(c_243, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.60  tff(c_252, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_243])).
% 3.32/1.60  tff(c_255, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_252])).
% 3.32/1.60  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.60  tff(c_259, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k2_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_255, c_10])).
% 3.32/1.60  tff(c_262, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_259])).
% 3.32/1.60  tff(c_361, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_355, c_262])).
% 3.32/1.60  tff(c_310, plain, (![A_23, B_24, D_89]: (k2_xboole_0(k2_tarski(A_23, B_24), k1_tarski(D_89))=k1_enumset1(A_23, B_24, D_89))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_301])).
% 3.32/1.60  tff(c_385, plain, (![D_89]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_89))=k1_enumset1('#skF_4', '#skF_3', D_89))), inference(superposition, [status(thm), theory('equality')], [c_361, c_310])).
% 3.32/1.60  tff(c_407, plain, (![D_104]: (k1_enumset1('#skF_4', '#skF_3', D_104)=k2_tarski('#skF_4', D_104))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_385])).
% 3.32/1.60  tff(c_18, plain, (![E_17, A_11, C_13]: (r2_hidden(E_17, k1_enumset1(A_11, E_17, C_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.32/1.60  tff(c_422, plain, (![D_104]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_104)))), inference(superposition, [status(thm), theory('equality')], [c_407, c_18])).
% 3.32/1.60  tff(c_311, plain, (![E_90, C_91, B_92, A_93]: (E_90=C_91 | E_90=B_92 | E_90=A_93 | ~r2_hidden(E_90, k1_enumset1(A_93, B_92, C_91)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.32/1.60  tff(c_978, plain, (![E_149, B_150, A_151]: (E_149=B_150 | E_149=A_151 | E_149=A_151 | ~r2_hidden(E_149, k2_tarski(A_151, B_150)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_311])).
% 3.32/1.60  tff(c_993, plain, (![D_104]: (D_104='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_422, c_978])).
% 3.32/1.60  tff(c_1017, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_993])).
% 3.32/1.60  tff(c_1011, plain, (![D_104]: (D_104='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_993])).
% 3.32/1.60  tff(c_1224, plain, (![D_2822]: (D_2822='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1017, c_1011])).
% 3.32/1.60  tff(c_1415, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1224, c_54])).
% 3.32/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.60  
% 3.32/1.60  Inference rules
% 3.32/1.60  ----------------------
% 3.32/1.60  #Ref     : 0
% 3.32/1.60  #Sup     : 412
% 3.32/1.60  #Fact    : 0
% 3.32/1.60  #Define  : 0
% 3.32/1.60  #Split   : 0
% 3.32/1.60  #Chain   : 0
% 3.32/1.60  #Close   : 0
% 3.32/1.60  
% 3.32/1.60  Ordering : KBO
% 3.32/1.60  
% 3.32/1.60  Simplification rules
% 3.32/1.60  ----------------------
% 3.32/1.60  #Subsume      : 88
% 3.32/1.60  #Demod        : 121
% 3.32/1.60  #Tautology    : 192
% 3.32/1.60  #SimpNegUnit  : 9
% 3.32/1.60  #BackRed      : 0
% 3.32/1.60  
% 3.32/1.60  #Partial instantiations: 51
% 3.32/1.60  #Strategies tried      : 1
% 3.32/1.60  
% 3.32/1.60  Timing (in seconds)
% 3.32/1.60  ----------------------
% 3.32/1.60  Preprocessing        : 0.31
% 3.32/1.60  Parsing              : 0.16
% 3.32/1.60  CNF conversion       : 0.02
% 3.32/1.60  Main loop            : 0.45
% 3.32/1.60  Inferencing          : 0.19
% 3.32/1.60  Reduction            : 0.15
% 3.32/1.60  Demodulation         : 0.12
% 3.32/1.60  BG Simplification    : 0.02
% 3.32/1.60  Subsumption          : 0.06
% 3.32/1.60  Abstraction          : 0.02
% 3.32/1.60  MUC search           : 0.00
% 3.32/1.60  Cooper               : 0.00
% 3.32/1.60  Total                : 0.79
% 3.32/1.60  Index Insertion      : 0.00
% 3.32/1.60  Index Deletion       : 0.00
% 3.32/1.60  Index Matching       : 0.00
% 3.32/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
