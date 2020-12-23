%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:25 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 118 expanded)
%              Number of leaves         :   42 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 153 expanded)
%              Number of equality atoms :   51 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_84,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_86,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_84,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_24,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_426,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_xboole_0(A_116,B_117)
      | ~ r2_hidden(C_118,k3_xboole_0(A_116,B_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_463,plain,(
    ! [A_122,B_123] :
      ( ~ r1_xboole_0(A_122,B_123)
      | k3_xboole_0(A_122,B_123) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_426])).

tff(c_467,plain,(
    ! [A_24] : k3_xboole_0(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_463])).

tff(c_22,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_468,plain,(
    ! [A_124] : k3_xboole_0(A_124,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_463])).

tff(c_14,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_476,plain,(
    ! [A_124] : k5_xboole_0(A_124,k1_xboole_0) = k4_xboole_0(A_124,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_14])).

tff(c_509,plain,(
    ! [A_125] : k4_xboole_0(A_125,k1_xboole_0) = A_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_476])).

tff(c_20,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_515,plain,(
    ! [A_125] : k4_xboole_0(A_125,A_125) = k3_xboole_0(A_125,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_20])).

tff(c_523,plain,(
    ! [A_125] : k4_xboole_0(A_125,A_125) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_515])).

tff(c_80,plain,(
    ! [B_72] : k4_xboole_0(k1_tarski(B_72),k1_tarski(B_72)) != k1_tarski(B_72) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_638,plain,(
    ! [B_72] : k1_tarski(B_72) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_80])).

tff(c_76,plain,(
    ! [B_69,C_70] : r1_tarski(k1_tarski(B_69),k2_tarski(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_88,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_209,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(A_95,B_96) = A_95
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_234,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_209])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_578,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_tarski(A_127,B_128)
      | ~ r1_tarski(A_127,k3_xboole_0(B_128,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1084,plain,(
    ! [A_160,B_161,A_162] :
      ( r1_tarski(A_160,B_161)
      | ~ r1_tarski(A_160,k3_xboole_0(A_162,B_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_578])).

tff(c_1189,plain,(
    ! [A_165] :
      ( r1_tarski(A_165,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_165,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1084])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1639,plain,(
    ! [A_192] :
      ( k3_xboole_0(A_192,k2_tarski('#skF_7','#skF_8')) = A_192
      | ~ r1_tarski(A_192,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1189,c_18])).

tff(c_1663,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1639])).

tff(c_48,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,(
    ! [B_66,C_67] :
      ( k4_xboole_0(k2_tarski(B_66,B_66),C_67) = k1_tarski(B_66)
      | r2_hidden(B_66,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1109,plain,(
    ! [B_163,C_164] :
      ( k4_xboole_0(k1_tarski(B_163),C_164) = k1_tarski(B_163)
      | r2_hidden(B_163,C_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_66])).

tff(c_1135,plain,(
    ! [B_163,C_164] :
      ( k4_xboole_0(k1_tarski(B_163),k1_tarski(B_163)) = k3_xboole_0(k1_tarski(B_163),C_164)
      | r2_hidden(B_163,C_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1109,c_20])).

tff(c_1177,plain,(
    ! [B_163,C_164] :
      ( k3_xboole_0(k1_tarski(B_163),C_164) = k1_xboole_0
      | r2_hidden(B_163,C_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_1135])).

tff(c_1670,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1663,c_1177])).

tff(c_1694,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_1670])).

tff(c_28,plain,(
    ! [D_32,B_28,A_27] :
      ( D_32 = B_28
      | D_32 = A_27
      | ~ r2_hidden(D_32,k2_tarski(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1700,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1694,c_28])).

tff(c_1704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_1700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.29/1.53  
% 3.29/1.53  %Foreground sorts:
% 3.29/1.53  
% 3.29/1.53  
% 3.29/1.53  %Background operators:
% 3.29/1.53  
% 3.29/1.53  
% 3.29/1.53  %Foreground operators:
% 3.29/1.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.29/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.29/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.29/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.29/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.53  
% 3.29/1.54  tff(f_135, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.29/1.54  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.29/1.54  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.29/1.54  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.29/1.54  tff(f_67, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.29/1.54  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.29/1.54  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.29/1.54  tff(f_125, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.29/1.54  tff(f_120, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.29/1.54  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.29/1.54  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.29/1.54  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.29/1.54  tff(f_84, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.29/1.54  tff(f_105, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 3.29/1.54  tff(f_80, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.29/1.54  tff(c_86, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.29/1.54  tff(c_84, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.29/1.54  tff(c_24, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.54  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.29/1.54  tff(c_426, plain, (![A_116, B_117, C_118]: (~r1_xboole_0(A_116, B_117) | ~r2_hidden(C_118, k3_xboole_0(A_116, B_117)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.54  tff(c_463, plain, (![A_122, B_123]: (~r1_xboole_0(A_122, B_123) | k3_xboole_0(A_122, B_123)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_426])).
% 3.29/1.54  tff(c_467, plain, (![A_24]: (k3_xboole_0(A_24, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_463])).
% 3.29/1.54  tff(c_22, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.29/1.54  tff(c_468, plain, (![A_124]: (k3_xboole_0(A_124, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_463])).
% 3.29/1.54  tff(c_14, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.54  tff(c_476, plain, (![A_124]: (k5_xboole_0(A_124, k1_xboole_0)=k4_xboole_0(A_124, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_468, c_14])).
% 3.29/1.54  tff(c_509, plain, (![A_125]: (k4_xboole_0(A_125, k1_xboole_0)=A_125)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_476])).
% 3.29/1.54  tff(c_20, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.54  tff(c_515, plain, (![A_125]: (k4_xboole_0(A_125, A_125)=k3_xboole_0(A_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_509, c_20])).
% 3.29/1.54  tff(c_523, plain, (![A_125]: (k4_xboole_0(A_125, A_125)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_467, c_515])).
% 3.29/1.54  tff(c_80, plain, (![B_72]: (k4_xboole_0(k1_tarski(B_72), k1_tarski(B_72))!=k1_tarski(B_72))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.29/1.54  tff(c_638, plain, (![B_72]: (k1_tarski(B_72)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_523, c_80])).
% 3.29/1.54  tff(c_76, plain, (![B_69, C_70]: (r1_tarski(k1_tarski(B_69), k2_tarski(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.29/1.54  tff(c_88, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.29/1.54  tff(c_209, plain, (![A_95, B_96]: (k3_xboole_0(A_95, B_96)=A_95 | ~r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.54  tff(c_234, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_88, c_209])).
% 3.29/1.54  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.54  tff(c_578, plain, (![A_127, B_128, C_129]: (r1_tarski(A_127, B_128) | ~r1_tarski(A_127, k3_xboole_0(B_128, C_129)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.54  tff(c_1084, plain, (![A_160, B_161, A_162]: (r1_tarski(A_160, B_161) | ~r1_tarski(A_160, k3_xboole_0(A_162, B_161)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_578])).
% 3.29/1.54  tff(c_1189, plain, (![A_165]: (r1_tarski(A_165, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_165, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_234, c_1084])).
% 3.29/1.54  tff(c_18, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.29/1.54  tff(c_1639, plain, (![A_192]: (k3_xboole_0(A_192, k2_tarski('#skF_7', '#skF_8'))=A_192 | ~r1_tarski(A_192, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1189, c_18])).
% 3.29/1.54  tff(c_1663, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1639])).
% 3.29/1.54  tff(c_48, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.29/1.54  tff(c_66, plain, (![B_66, C_67]: (k4_xboole_0(k2_tarski(B_66, B_66), C_67)=k1_tarski(B_66) | r2_hidden(B_66, C_67))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.29/1.54  tff(c_1109, plain, (![B_163, C_164]: (k4_xboole_0(k1_tarski(B_163), C_164)=k1_tarski(B_163) | r2_hidden(B_163, C_164))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_66])).
% 3.29/1.54  tff(c_1135, plain, (![B_163, C_164]: (k4_xboole_0(k1_tarski(B_163), k1_tarski(B_163))=k3_xboole_0(k1_tarski(B_163), C_164) | r2_hidden(B_163, C_164))), inference(superposition, [status(thm), theory('equality')], [c_1109, c_20])).
% 3.29/1.54  tff(c_1177, plain, (![B_163, C_164]: (k3_xboole_0(k1_tarski(B_163), C_164)=k1_xboole_0 | r2_hidden(B_163, C_164))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_1135])).
% 3.29/1.54  tff(c_1670, plain, (k1_tarski('#skF_5')=k1_xboole_0 | r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1663, c_1177])).
% 3.29/1.54  tff(c_1694, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_638, c_1670])).
% 3.29/1.54  tff(c_28, plain, (![D_32, B_28, A_27]: (D_32=B_28 | D_32=A_27 | ~r2_hidden(D_32, k2_tarski(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.29/1.54  tff(c_1700, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1694, c_28])).
% 3.29/1.54  tff(c_1704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_1700])).
% 3.29/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.54  
% 3.29/1.54  Inference rules
% 3.29/1.54  ----------------------
% 3.29/1.54  #Ref     : 0
% 3.29/1.54  #Sup     : 379
% 3.29/1.54  #Fact    : 0
% 3.29/1.54  #Define  : 0
% 3.29/1.54  #Split   : 2
% 3.29/1.54  #Chain   : 0
% 3.29/1.54  #Close   : 0
% 3.29/1.54  
% 3.29/1.54  Ordering : KBO
% 3.29/1.54  
% 3.29/1.54  Simplification rules
% 3.29/1.54  ----------------------
% 3.29/1.54  #Subsume      : 52
% 3.29/1.54  #Demod        : 148
% 3.29/1.54  #Tautology    : 251
% 3.29/1.54  #SimpNegUnit  : 35
% 3.29/1.54  #BackRed      : 3
% 3.29/1.54  
% 3.29/1.54  #Partial instantiations: 0
% 3.29/1.54  #Strategies tried      : 1
% 3.29/1.54  
% 3.29/1.54  Timing (in seconds)
% 3.29/1.54  ----------------------
% 3.43/1.54  Preprocessing        : 0.36
% 3.43/1.54  Parsing              : 0.19
% 3.43/1.54  CNF conversion       : 0.03
% 3.43/1.54  Main loop            : 0.42
% 3.43/1.54  Inferencing          : 0.15
% 3.43/1.54  Reduction            : 0.15
% 3.43/1.54  Demodulation         : 0.11
% 3.43/1.54  BG Simplification    : 0.03
% 3.43/1.54  Subsumption          : 0.07
% 3.43/1.54  Abstraction          : 0.02
% 3.43/1.54  MUC search           : 0.00
% 3.43/1.55  Cooper               : 0.00
% 3.43/1.55  Total                : 0.81
% 3.43/1.55  Index Insertion      : 0.00
% 3.43/1.55  Index Deletion       : 0.00
% 3.43/1.55  Index Matching       : 0.00
% 3.43/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
