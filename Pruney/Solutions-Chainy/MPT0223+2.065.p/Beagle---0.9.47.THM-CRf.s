%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:25 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 183 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :   62 ( 199 expanded)
%              Number of equality atoms :   56 ( 186 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    ! [A_28,B_29,C_30] : k2_enumset1(A_28,A_28,B_29,C_30) = k1_enumset1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_721,plain,(
    ! [A_108,B_109,C_110,D_111] : k2_xboole_0(k1_enumset1(A_108,B_109,C_110),k1_tarski(D_111)) = k2_enumset1(A_108,B_109,C_110,D_111) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_754,plain,(
    ! [A_26,B_27,D_111] : k2_xboole_0(k2_tarski(A_26,B_27),k1_tarski(D_111)) = k2_enumset1(A_26,A_26,B_27,D_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_721])).

tff(c_774,plain,(
    ! [A_117,B_118,D_119] : k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(D_119)) = k1_enumset1(A_117,B_118,D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_754])).

tff(c_798,plain,(
    ! [A_25,D_119] : k2_xboole_0(k1_tarski(A_25),k1_tarski(D_119)) = k1_enumset1(A_25,A_25,D_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_774])).

tff(c_804,plain,(
    ! [A_25,D_119] : k2_xboole_0(k1_tarski(A_25),k1_tarski(D_119)) = k2_tarski(A_25,D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_798])).

tff(c_805,plain,(
    ! [A_120,D_121] : k2_xboole_0(k1_tarski(A_120),k1_tarski(D_121)) = k2_tarski(A_120,D_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_798])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_273,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_258])).

tff(c_277,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_273])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_270,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_258])).

tff(c_276,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_270])).

tff(c_58,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_267,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_258])).

tff(c_387,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_267])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_391,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_12])).

tff(c_394,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_391])).

tff(c_823,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_394])).

tff(c_760,plain,(
    ! [A_26,B_27,D_111] : k2_xboole_0(k2_tarski(A_26,B_27),k1_tarski(D_111)) = k1_enumset1(A_26,B_27,D_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_754])).

tff(c_849,plain,(
    ! [D_111] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_111)) = k1_enumset1('#skF_4','#skF_3',D_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_760])).

tff(c_901,plain,(
    ! [D_131] : k1_enumset1('#skF_4','#skF_3',D_131) = k2_tarski('#skF_4',D_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_849])).

tff(c_18,plain,(
    ! [E_17,A_11,C_13] : r2_hidden(E_17,k1_enumset1(A_11,E_17,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_926,plain,(
    ! [D_131] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_18])).

tff(c_534,plain,(
    ! [E_99,C_100,B_101,A_102] :
      ( E_99 = C_100
      | E_99 = B_101
      | E_99 = A_102
      | ~ r2_hidden(E_99,k1_enumset1(A_102,B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2683,plain,(
    ! [E_233,B_234,A_235] :
      ( E_233 = B_234
      | E_233 = A_235
      | E_233 = A_235
      | ~ r2_hidden(E_233,k2_tarski(A_235,B_234)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_534])).

tff(c_2690,plain,(
    ! [D_131] :
      ( D_131 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_926,c_2683])).

tff(c_2715,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_2690])).

tff(c_2709,plain,(
    ! [D_131] : D_131 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_2690])).

tff(c_3129,plain,(
    ! [D_4720] : D_4720 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2715,c_2709])).

tff(c_3524,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3129,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.81  
% 4.46/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.82  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.56/1.82  
% 4.56/1.82  %Foreground sorts:
% 4.56/1.82  
% 4.56/1.82  
% 4.56/1.82  %Background operators:
% 4.56/1.82  
% 4.56/1.82  
% 4.56/1.82  %Foreground operators:
% 4.56/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.56/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.56/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.56/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.56/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.56/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.56/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.56/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.56/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.56/1.82  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.56/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.56/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.56/1.82  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.56/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.56/1.82  
% 4.59/1.83  tff(f_75, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 4.59/1.83  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.59/1.83  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.59/1.83  tff(f_62, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.59/1.83  tff(f_56, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.59/1.83  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.59/1.83  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.59/1.83  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.59/1.83  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.59/1.83  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.59/1.83  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.59/1.83  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.59/1.83  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.59/1.83  tff(c_44, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.59/1.83  tff(c_42, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.59/1.83  tff(c_46, plain, (![A_28, B_29, C_30]: (k2_enumset1(A_28, A_28, B_29, C_30)=k1_enumset1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.59/1.83  tff(c_721, plain, (![A_108, B_109, C_110, D_111]: (k2_xboole_0(k1_enumset1(A_108, B_109, C_110), k1_tarski(D_111))=k2_enumset1(A_108, B_109, C_110, D_111))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.59/1.83  tff(c_754, plain, (![A_26, B_27, D_111]: (k2_xboole_0(k2_tarski(A_26, B_27), k1_tarski(D_111))=k2_enumset1(A_26, A_26, B_27, D_111))), inference(superposition, [status(thm), theory('equality')], [c_44, c_721])).
% 4.59/1.83  tff(c_774, plain, (![A_117, B_118, D_119]: (k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(D_119))=k1_enumset1(A_117, B_118, D_119))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_754])).
% 4.59/1.83  tff(c_798, plain, (![A_25, D_119]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(D_119))=k1_enumset1(A_25, A_25, D_119))), inference(superposition, [status(thm), theory('equality')], [c_42, c_774])).
% 4.59/1.83  tff(c_804, plain, (![A_25, D_119]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(D_119))=k2_tarski(A_25, D_119))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_798])).
% 4.59/1.83  tff(c_805, plain, (![A_120, D_121]: (k2_xboole_0(k1_tarski(A_120), k1_tarski(D_121))=k2_tarski(A_120, D_121))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_798])).
% 4.59/1.83  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.59/1.83  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.59/1.83  tff(c_258, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.59/1.83  tff(c_273, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_258])).
% 4.59/1.83  tff(c_277, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_273])).
% 4.59/1.83  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.59/1.83  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.59/1.83  tff(c_270, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_258])).
% 4.59/1.83  tff(c_276, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_270])).
% 4.59/1.83  tff(c_58, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.59/1.83  tff(c_267, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_258])).
% 4.59/1.83  tff(c_387, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_276, c_267])).
% 4.59/1.83  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.59/1.83  tff(c_391, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_387, c_12])).
% 4.59/1.83  tff(c_394, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_391])).
% 4.59/1.83  tff(c_823, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_805, c_394])).
% 4.59/1.83  tff(c_760, plain, (![A_26, B_27, D_111]: (k2_xboole_0(k2_tarski(A_26, B_27), k1_tarski(D_111))=k1_enumset1(A_26, B_27, D_111))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_754])).
% 4.59/1.83  tff(c_849, plain, (![D_111]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_111))=k1_enumset1('#skF_4', '#skF_3', D_111))), inference(superposition, [status(thm), theory('equality')], [c_823, c_760])).
% 4.59/1.83  tff(c_901, plain, (![D_131]: (k1_enumset1('#skF_4', '#skF_3', D_131)=k2_tarski('#skF_4', D_131))), inference(demodulation, [status(thm), theory('equality')], [c_804, c_849])).
% 4.59/1.83  tff(c_18, plain, (![E_17, A_11, C_13]: (r2_hidden(E_17, k1_enumset1(A_11, E_17, C_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.59/1.83  tff(c_926, plain, (![D_131]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_131)))), inference(superposition, [status(thm), theory('equality')], [c_901, c_18])).
% 4.59/1.83  tff(c_534, plain, (![E_99, C_100, B_101, A_102]: (E_99=C_100 | E_99=B_101 | E_99=A_102 | ~r2_hidden(E_99, k1_enumset1(A_102, B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.59/1.83  tff(c_2683, plain, (![E_233, B_234, A_235]: (E_233=B_234 | E_233=A_235 | E_233=A_235 | ~r2_hidden(E_233, k2_tarski(A_235, B_234)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_534])).
% 4.59/1.83  tff(c_2690, plain, (![D_131]: (D_131='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_926, c_2683])).
% 4.59/1.83  tff(c_2715, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_2690])).
% 4.59/1.83  tff(c_2709, plain, (![D_131]: (D_131='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_2690])).
% 4.59/1.83  tff(c_3129, plain, (![D_4720]: (D_4720='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2715, c_2709])).
% 4.59/1.83  tff(c_3524, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3129, c_56])).
% 4.59/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.83  
% 4.59/1.83  Inference rules
% 4.59/1.83  ----------------------
% 4.59/1.83  #Ref     : 0
% 4.59/1.83  #Sup     : 1011
% 4.59/1.83  #Fact    : 0
% 4.59/1.83  #Define  : 0
% 4.59/1.83  #Split   : 0
% 4.59/1.83  #Chain   : 0
% 4.59/1.83  #Close   : 0
% 4.59/1.83  
% 4.59/1.83  Ordering : KBO
% 4.59/1.83  
% 4.59/1.83  Simplification rules
% 4.59/1.83  ----------------------
% 4.59/1.83  #Subsume      : 149
% 4.59/1.83  #Demod        : 775
% 4.59/1.83  #Tautology    : 556
% 4.59/1.83  #SimpNegUnit  : 9
% 4.59/1.83  #BackRed      : 0
% 4.59/1.83  
% 4.59/1.83  #Partial instantiations: 86
% 4.59/1.83  #Strategies tried      : 1
% 4.59/1.83  
% 4.59/1.83  Timing (in seconds)
% 4.59/1.83  ----------------------
% 4.59/1.83  Preprocessing        : 0.32
% 4.59/1.83  Parsing              : 0.16
% 4.59/1.83  CNF conversion       : 0.02
% 4.59/1.83  Main loop            : 0.76
% 4.59/1.83  Inferencing          : 0.29
% 4.59/1.83  Reduction            : 0.30
% 4.59/1.83  Demodulation         : 0.24
% 4.59/1.83  BG Simplification    : 0.03
% 4.59/1.83  Subsumption          : 0.10
% 4.59/1.83  Abstraction          : 0.04
% 4.59/1.83  MUC search           : 0.00
% 4.59/1.83  Cooper               : 0.00
% 4.59/1.83  Total                : 1.10
% 4.59/1.83  Index Insertion      : 0.00
% 4.59/1.83  Index Deletion       : 0.00
% 4.59/1.83  Index Matching       : 0.00
% 4.59/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
