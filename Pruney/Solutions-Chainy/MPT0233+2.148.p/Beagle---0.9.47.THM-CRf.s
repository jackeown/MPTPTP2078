%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:40 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 291 expanded)
%              Number of leaves         :   32 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 587 expanded)
%              Number of equality atoms :   66 ( 441 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] : k5_enumset1(A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

tff(f_71,axiom,(
    ! [A] : k5_enumset1(A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_66,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_68,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_360,plain,(
    ! [B_104,C_105,A_106] :
      ( k2_tarski(B_104,C_105) = A_106
      | k1_tarski(C_105) = A_106
      | k1_tarski(B_104) = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,k2_tarski(B_104,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_384,plain,
    ( k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_360])).

tff(c_450,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_28,plain,(
    ! [D_18,A_13] : r2_hidden(D_18,k2_tarski(A_13,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_479,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_28])).

tff(c_16,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,(
    ! [A_45,B_46] : r1_xboole_0(k3_xboole_0(A_45,B_46),k4_xboole_0(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_91,plain,(
    ! [A_6] : r1_xboole_0(k3_xboole_0(k1_xboole_0,A_6),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_88])).

tff(c_103,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | r1_xboole_0(A_52,k3_xboole_0(B_53,C_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_129,plain,(
    ! [B_60,C_61] :
      ( k3_xboole_0(B_60,C_61) = k1_xboole_0
      | ~ r1_xboole_0(k3_xboole_0(B_60,C_61),B_60) ) ),
    inference(resolution,[status(thm)],[c_103,c_20])).

tff(c_150,plain,(
    ! [A_63] : k3_xboole_0(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_129])).

tff(c_14,plain,(
    ! [A_4,B_5] : k5_xboole_0(A_4,k3_xboole_0(A_4,B_5)) = k4_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_158,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_14])).

tff(c_170,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_158])).

tff(c_188,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ r2_hidden(A_67,C_68)
      | ~ r2_hidden(A_67,B_69)
      | ~ r2_hidden(A_67,k5_xboole_0(B_69,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_191,plain,(
    ! [A_67] :
      ( ~ r2_hidden(A_67,k1_xboole_0)
      | ~ r2_hidden(A_67,k1_xboole_0)
      | ~ r2_hidden(A_67,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_188])).

tff(c_491,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_479,c_191])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_491])).

tff(c_496,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_3094,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_3129,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3094,c_28])).

tff(c_26,plain,(
    ! [D_18,B_14,A_13] :
      ( D_18 = B_14
      | D_18 = A_13
      | ~ r2_hidden(D_18,k2_tarski(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3251,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3129,c_26])).

tff(c_3333,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3251])).

tff(c_3340,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3333,c_64])).

tff(c_233,plain,(
    ! [A_80,B_81,C_82] : k5_enumset1(A_80,A_80,A_80,A_80,A_80,B_81,C_82) = k1_enumset1(A_80,B_81,C_82) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,(
    ! [A_24] : k5_enumset1(A_24,A_24,A_24,A_24,A_24,A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_260,plain,(
    ! [C_86] : k1_enumset1(C_86,C_86,C_86) = k1_tarski(C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_48])).

tff(c_44,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_266,plain,(
    ! [C_86] : k2_tarski(C_86,C_86) = k1_tarski(C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_44])).

tff(c_30,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3132,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3094,c_30])).

tff(c_3349,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3132,c_26])).

tff(c_3431,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3349])).

tff(c_3335,plain,(
    k2_tarski('#skF_5','#skF_4') = k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3333,c_3094])).

tff(c_3450,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_3431,c_3335])).

tff(c_3487,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3450,c_30])).

tff(c_276,plain,(
    ! [C_87] : k2_tarski(C_87,C_87) = k1_tarski(C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_44])).

tff(c_285,plain,(
    ! [D_18,C_87] :
      ( D_18 = C_87
      | D_18 = C_87
      | ~ r2_hidden(D_18,k1_tarski(C_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_26])).

tff(c_3602,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3487,c_285])).

tff(c_3644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3340,c_3340,c_3602])).

tff(c_3645,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_3656,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3645])).

tff(c_3696,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3656,c_30])).

tff(c_3803,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3696,c_285])).

tff(c_3845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_3803])).

tff(c_3846,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_3645])).

tff(c_3884,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3846,c_28])).

tff(c_4035,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3884,c_285])).

tff(c_4043,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4035,c_64])).

tff(c_3887,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3846,c_30])).

tff(c_4054,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4035,c_3887])).

tff(c_4057,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4054,c_285])).

tff(c_4099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4043,c_4043,c_4057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:41:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.86  
% 4.64/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.64/1.86  
% 4.64/1.86  %Foreground sorts:
% 4.64/1.86  
% 4.64/1.86  
% 4.64/1.86  %Background operators:
% 4.64/1.86  
% 4.64/1.86  
% 4.64/1.86  %Foreground operators:
% 4.64/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.64/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.64/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.64/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.64/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.64/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.64/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.64/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.64/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.64/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.64/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.64/1.86  
% 4.64/1.88  tff(f_107, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.64/1.88  tff(f_86, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.64/1.88  tff(f_65, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.64/1.88  tff(f_36, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.64/1.88  tff(f_56, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 4.64/1.88  tff(f_54, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 4.64/1.88  tff(f_48, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.64/1.88  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.64/1.88  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.64/1.88  tff(f_69, axiom, (![A, B, C]: (k5_enumset1(A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_enumset1)).
% 4.64/1.88  tff(f_71, axiom, (![A]: (k5_enumset1(A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_enumset1)).
% 4.64/1.88  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.64/1.88  tff(c_66, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.64/1.88  tff(c_64, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.64/1.88  tff(c_68, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.64/1.88  tff(c_360, plain, (![B_104, C_105, A_106]: (k2_tarski(B_104, C_105)=A_106 | k1_tarski(C_105)=A_106 | k1_tarski(B_104)=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, k2_tarski(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.64/1.88  tff(c_384, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_360])).
% 4.64/1.88  tff(c_450, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_384])).
% 4.64/1.88  tff(c_28, plain, (![D_18, A_13]: (r2_hidden(D_18, k2_tarski(A_13, D_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.64/1.88  tff(c_479, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_450, c_28])).
% 4.64/1.88  tff(c_16, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.88  tff(c_88, plain, (![A_45, B_46]: (r1_xboole_0(k3_xboole_0(A_45, B_46), k4_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.64/1.88  tff(c_91, plain, (![A_6]: (r1_xboole_0(k3_xboole_0(k1_xboole_0, A_6), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_88])).
% 4.64/1.88  tff(c_103, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | r1_xboole_0(A_52, k3_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.64/1.88  tff(c_20, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.64/1.88  tff(c_129, plain, (![B_60, C_61]: (k3_xboole_0(B_60, C_61)=k1_xboole_0 | ~r1_xboole_0(k3_xboole_0(B_60, C_61), B_60))), inference(resolution, [status(thm)], [c_103, c_20])).
% 4.64/1.88  tff(c_150, plain, (![A_63]: (k3_xboole_0(k1_xboole_0, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_129])).
% 4.64/1.88  tff(c_14, plain, (![A_4, B_5]: (k5_xboole_0(A_4, k3_xboole_0(A_4, B_5))=k4_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.64/1.88  tff(c_158, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_63))), inference(superposition, [status(thm), theory('equality')], [c_150, c_14])).
% 4.64/1.88  tff(c_170, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_158])).
% 4.64/1.88  tff(c_188, plain, (![A_67, C_68, B_69]: (~r2_hidden(A_67, C_68) | ~r2_hidden(A_67, B_69) | ~r2_hidden(A_67, k5_xboole_0(B_69, C_68)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.64/1.88  tff(c_191, plain, (![A_67]: (~r2_hidden(A_67, k1_xboole_0) | ~r2_hidden(A_67, k1_xboole_0) | ~r2_hidden(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_170, c_188])).
% 4.64/1.88  tff(c_491, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_479, c_191])).
% 4.64/1.88  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_479, c_491])).
% 4.64/1.88  tff(c_496, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_384])).
% 4.64/1.88  tff(c_3094, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_496])).
% 4.64/1.88  tff(c_3129, plain, (r2_hidden('#skF_6', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3094, c_28])).
% 4.64/1.88  tff(c_26, plain, (![D_18, B_14, A_13]: (D_18=B_14 | D_18=A_13 | ~r2_hidden(D_18, k2_tarski(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.64/1.88  tff(c_3251, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_3129, c_26])).
% 4.64/1.88  tff(c_3333, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_64, c_3251])).
% 4.64/1.88  tff(c_3340, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3333, c_64])).
% 4.64/1.88  tff(c_233, plain, (![A_80, B_81, C_82]: (k5_enumset1(A_80, A_80, A_80, A_80, A_80, B_81, C_82)=k1_enumset1(A_80, B_81, C_82))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.64/1.88  tff(c_48, plain, (![A_24]: (k5_enumset1(A_24, A_24, A_24, A_24, A_24, A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.88  tff(c_260, plain, (![C_86]: (k1_enumset1(C_86, C_86, C_86)=k1_tarski(C_86))), inference(superposition, [status(thm), theory('equality')], [c_233, c_48])).
% 4.64/1.88  tff(c_44, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.64/1.88  tff(c_266, plain, (![C_86]: (k2_tarski(C_86, C_86)=k1_tarski(C_86))), inference(superposition, [status(thm), theory('equality')], [c_260, c_44])).
% 4.64/1.88  tff(c_30, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.64/1.88  tff(c_3132, plain, (r2_hidden('#skF_5', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3094, c_30])).
% 4.64/1.88  tff(c_3349, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_3132, c_26])).
% 4.64/1.88  tff(c_3431, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_66, c_3349])).
% 4.64/1.88  tff(c_3335, plain, (k2_tarski('#skF_5', '#skF_4')=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3333, c_3094])).
% 4.64/1.88  tff(c_3450, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_3431, c_3335])).
% 4.64/1.88  tff(c_3487, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3450, c_30])).
% 4.64/1.88  tff(c_276, plain, (![C_87]: (k2_tarski(C_87, C_87)=k1_tarski(C_87))), inference(superposition, [status(thm), theory('equality')], [c_260, c_44])).
% 4.64/1.88  tff(c_285, plain, (![D_18, C_87]: (D_18=C_87 | D_18=C_87 | ~r2_hidden(D_18, k1_tarski(C_87)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_26])).
% 4.64/1.88  tff(c_3602, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_3487, c_285])).
% 4.64/1.88  tff(c_3644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3340, c_3340, c_3602])).
% 4.64/1.88  tff(c_3645, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_496])).
% 4.64/1.88  tff(c_3656, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_3645])).
% 4.64/1.88  tff(c_3696, plain, (r2_hidden('#skF_3', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3656, c_30])).
% 4.64/1.88  tff(c_3803, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_3696, c_285])).
% 4.64/1.88  tff(c_3845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_3803])).
% 4.64/1.88  tff(c_3846, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_3645])).
% 4.64/1.88  tff(c_3884, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3846, c_28])).
% 4.64/1.88  tff(c_4035, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_3884, c_285])).
% 4.64/1.88  tff(c_4043, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4035, c_64])).
% 4.64/1.88  tff(c_3887, plain, (r2_hidden('#skF_3', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3846, c_30])).
% 4.64/1.88  tff(c_4054, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4035, c_3887])).
% 4.64/1.88  tff(c_4057, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4054, c_285])).
% 4.64/1.88  tff(c_4099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4043, c_4043, c_4057])).
% 4.64/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.88  
% 4.64/1.88  Inference rules
% 4.64/1.88  ----------------------
% 4.64/1.88  #Ref     : 0
% 4.64/1.88  #Sup     : 548
% 4.64/1.88  #Fact    : 4
% 4.64/1.88  #Define  : 0
% 4.64/1.88  #Split   : 13
% 4.64/1.88  #Chain   : 0
% 4.64/1.88  #Close   : 0
% 4.64/1.88  
% 4.64/1.88  Ordering : KBO
% 4.64/1.88  
% 4.64/1.88  Simplification rules
% 4.64/1.88  ----------------------
% 4.64/1.88  #Subsume      : 44
% 4.64/1.88  #Demod        : 190
% 4.64/1.88  #Tautology    : 168
% 4.64/1.88  #SimpNegUnit  : 7
% 4.64/1.88  #BackRed      : 30
% 4.64/1.88  
% 4.64/1.88  #Partial instantiations: 3696
% 4.64/1.88  #Strategies tried      : 1
% 4.64/1.88  
% 4.64/1.88  Timing (in seconds)
% 4.64/1.88  ----------------------
% 4.64/1.88  Preprocessing        : 0.33
% 4.64/1.88  Parsing              : 0.18
% 4.64/1.88  CNF conversion       : 0.02
% 4.64/1.88  Main loop            : 0.74
% 4.64/1.88  Inferencing          : 0.37
% 4.64/1.88  Reduction            : 0.18
% 4.64/1.88  Demodulation         : 0.14
% 4.64/1.88  BG Simplification    : 0.04
% 4.64/1.88  Subsumption          : 0.11
% 4.64/1.88  Abstraction          : 0.03
% 4.64/1.88  MUC search           : 0.00
% 4.64/1.88  Cooper               : 0.00
% 4.64/1.88  Total                : 1.11
% 4.64/1.88  Index Insertion      : 0.00
% 4.64/1.88  Index Deletion       : 0.00
% 4.64/1.88  Index Matching       : 0.00
% 4.64/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
