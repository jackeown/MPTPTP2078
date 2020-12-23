%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:35 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 413 expanded)
%              Number of leaves         :   36 ( 153 expanded)
%              Depth                    :   15
%              Number of atoms          :   94 ( 578 expanded)
%              Number of equality atoms :   61 ( 410 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_74,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_306,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_327,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_306])).

tff(c_332,plain,(
    ! [A_89] : k4_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_327])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_338,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k3_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_14])).

tff(c_343,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_338])).

tff(c_68,plain,(
    ! [B_57] : k4_xboole_0(k1_tarski(B_57),k1_tarski(B_57)) != k1_tarski(B_57) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_376,plain,(
    ! [B_57] : k1_tarski(B_57) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_68])).

tff(c_62,plain,(
    ! [C_55,B_54] : r1_tarski(k1_tarski(C_55),k2_tarski(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_76,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_238,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(A_78,B_79) = A_78
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_263,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_238])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_432,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski(A_94,B_95)
      | ~ r1_tarski(A_94,k3_xboole_0(B_95,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_617,plain,(
    ! [A_114,B_115,A_116] :
      ( r1_tarski(A_114,B_115)
      | ~ r1_tarski(A_114,k3_xboole_0(A_116,B_115)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_432])).

tff(c_801,plain,(
    ! [A_126] :
      ( r1_tarski(A_126,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_126,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_617])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1215,plain,(
    ! [A_157] :
      ( k3_xboole_0(A_157,k2_tarski('#skF_5','#skF_6')) = A_157
      | ~ r1_tarski(A_157,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_801,c_10])).

tff(c_1244,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1215])).

tff(c_36,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    ! [B_51,C_52] :
      ( k4_xboole_0(k2_tarski(B_51,B_51),C_52) = k1_tarski(B_51)
      | r2_hidden(B_51,C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_727,plain,(
    ! [B_124,C_125] :
      ( k4_xboole_0(k1_tarski(B_124),C_125) = k1_tarski(B_124)
      | r2_hidden(B_124,C_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54])).

tff(c_753,plain,(
    ! [B_124,C_125] :
      ( k4_xboole_0(k1_tarski(B_124),k1_tarski(B_124)) = k3_xboole_0(k1_tarski(B_124),C_125)
      | r2_hidden(B_124,C_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_14])).

tff(c_791,plain,(
    ! [B_124,C_125] :
      ( k3_xboole_0(k1_tarski(B_124),C_125) = k1_xboole_0
      | r2_hidden(B_124,C_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_753])).

tff(c_1254,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_791])).

tff(c_1273,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_1254])).

tff(c_18,plain,(
    ! [D_21,B_17,A_16] :
      ( D_21 = B_17
      | D_21 = A_16
      | ~ r2_hidden(D_21,k2_tarski(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1280,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1273,c_18])).

tff(c_1281,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1280])).

tff(c_1290,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1281,c_74])).

tff(c_72,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    ! [B_54,C_55] : r1_tarski(k1_tarski(B_54),k2_tarski(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1245,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1215])).

tff(c_1336,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_6')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1281,c_1245])).

tff(c_1343,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_791])).

tff(c_1362,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_1343])).

tff(c_1368,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1362,c_18])).

tff(c_1372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1290,c_72,c_1368])).

tff(c_1373,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1280])).

tff(c_1383,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_72])).

tff(c_1429,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_4')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_1245])).

tff(c_1436,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_791])).

tff(c_1455,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_1436])).

tff(c_1461,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1455,c_18])).

tff(c_1465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1383,c_1461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:52:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.56  
% 3.33/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.56  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.33/1.56  
% 3.33/1.56  %Foreground sorts:
% 3.33/1.56  
% 3.33/1.56  
% 3.33/1.56  %Background operators:
% 3.33/1.56  
% 3.33/1.56  
% 3.33/1.56  %Foreground operators:
% 3.33/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.33/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.33/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.33/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.33/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.33/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.33/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.56  
% 3.33/1.57  tff(f_107, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.33/1.57  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.33/1.57  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.33/1.57  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.33/1.57  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.33/1.57  tff(f_97, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.33/1.57  tff(f_92, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.33/1.57  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.33/1.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.33/1.57  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.33/1.57  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.33/1.57  tff(f_77, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 3.33/1.57  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.33/1.57  tff(c_74, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.57  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.57  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.33/1.57  tff(c_306, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.57  tff(c_327, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_306])).
% 3.33/1.57  tff(c_332, plain, (![A_89]: (k4_xboole_0(A_89, k1_xboole_0)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_327])).
% 3.33/1.57  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.57  tff(c_338, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k3_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_332, c_14])).
% 3.33/1.57  tff(c_343, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_338])).
% 3.33/1.57  tff(c_68, plain, (![B_57]: (k4_xboole_0(k1_tarski(B_57), k1_tarski(B_57))!=k1_tarski(B_57))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.33/1.57  tff(c_376, plain, (![B_57]: (k1_tarski(B_57)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_68])).
% 3.33/1.57  tff(c_62, plain, (![C_55, B_54]: (r1_tarski(k1_tarski(C_55), k2_tarski(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.33/1.57  tff(c_76, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.57  tff(c_238, plain, (![A_78, B_79]: (k3_xboole_0(A_78, B_79)=A_78 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.57  tff(c_263, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_238])).
% 3.33/1.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.33/1.57  tff(c_432, plain, (![A_94, B_95, C_96]: (r1_tarski(A_94, B_95) | ~r1_tarski(A_94, k3_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.57  tff(c_617, plain, (![A_114, B_115, A_116]: (r1_tarski(A_114, B_115) | ~r1_tarski(A_114, k3_xboole_0(A_116, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_432])).
% 3.33/1.57  tff(c_801, plain, (![A_126]: (r1_tarski(A_126, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_126, k2_tarski('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_263, c_617])).
% 3.33/1.57  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.57  tff(c_1215, plain, (![A_157]: (k3_xboole_0(A_157, k2_tarski('#skF_5', '#skF_6'))=A_157 | ~r1_tarski(A_157, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_801, c_10])).
% 3.33/1.57  tff(c_1244, plain, (k3_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1215])).
% 3.33/1.57  tff(c_36, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.33/1.57  tff(c_54, plain, (![B_51, C_52]: (k4_xboole_0(k2_tarski(B_51, B_51), C_52)=k1_tarski(B_51) | r2_hidden(B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.33/1.57  tff(c_727, plain, (![B_124, C_125]: (k4_xboole_0(k1_tarski(B_124), C_125)=k1_tarski(B_124) | r2_hidden(B_124, C_125))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54])).
% 3.33/1.57  tff(c_753, plain, (![B_124, C_125]: (k4_xboole_0(k1_tarski(B_124), k1_tarski(B_124))=k3_xboole_0(k1_tarski(B_124), C_125) | r2_hidden(B_124, C_125))), inference(superposition, [status(thm), theory('equality')], [c_727, c_14])).
% 3.33/1.57  tff(c_791, plain, (![B_124, C_125]: (k3_xboole_0(k1_tarski(B_124), C_125)=k1_xboole_0 | r2_hidden(B_124, C_125))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_753])).
% 3.33/1.57  tff(c_1254, plain, (k1_tarski('#skF_4')=k1_xboole_0 | r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1244, c_791])).
% 3.33/1.57  tff(c_1273, plain, (r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_376, c_1254])).
% 3.33/1.57  tff(c_18, plain, (![D_21, B_17, A_16]: (D_21=B_17 | D_21=A_16 | ~r2_hidden(D_21, k2_tarski(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.57  tff(c_1280, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1273, c_18])).
% 3.33/1.57  tff(c_1281, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1280])).
% 3.33/1.57  tff(c_1290, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1281, c_74])).
% 3.33/1.57  tff(c_72, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.57  tff(c_64, plain, (![B_54, C_55]: (r1_tarski(k1_tarski(B_54), k2_tarski(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.33/1.57  tff(c_1245, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1215])).
% 3.33/1.57  tff(c_1336, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_6'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1281, c_1245])).
% 3.33/1.57  tff(c_1343, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1336, c_791])).
% 3.33/1.57  tff(c_1362, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_376, c_1343])).
% 3.33/1.57  tff(c_1368, plain, ('#skF_6'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1362, c_18])).
% 3.33/1.57  tff(c_1372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1290, c_72, c_1368])).
% 3.33/1.57  tff(c_1373, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_1280])).
% 3.33/1.57  tff(c_1383, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1373, c_72])).
% 3.33/1.57  tff(c_1429, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_4'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1373, c_1245])).
% 3.33/1.57  tff(c_1436, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1429, c_791])).
% 3.33/1.57  tff(c_1455, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_376, c_1436])).
% 3.33/1.57  tff(c_1461, plain, ('#skF_3'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_1455, c_18])).
% 3.33/1.57  tff(c_1465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1383, c_1461])).
% 3.33/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.57  
% 3.33/1.57  Inference rules
% 3.33/1.57  ----------------------
% 3.33/1.57  #Ref     : 0
% 3.33/1.57  #Sup     : 322
% 3.33/1.57  #Fact    : 0
% 3.33/1.57  #Define  : 0
% 3.33/1.57  #Split   : 1
% 3.33/1.57  #Chain   : 0
% 3.33/1.57  #Close   : 0
% 3.33/1.57  
% 3.33/1.57  Ordering : KBO
% 3.33/1.57  
% 3.33/1.57  Simplification rules
% 3.33/1.58  ----------------------
% 3.33/1.58  #Subsume      : 37
% 3.33/1.58  #Demod        : 152
% 3.33/1.58  #Tautology    : 208
% 3.33/1.58  #SimpNegUnit  : 30
% 3.33/1.58  #BackRed      : 19
% 3.33/1.58  
% 3.33/1.58  #Partial instantiations: 0
% 3.33/1.58  #Strategies tried      : 1
% 3.33/1.58  
% 3.33/1.58  Timing (in seconds)
% 3.33/1.58  ----------------------
% 3.33/1.58  Preprocessing        : 0.35
% 3.33/1.58  Parsing              : 0.18
% 3.33/1.58  CNF conversion       : 0.03
% 3.33/1.58  Main loop            : 0.46
% 3.33/1.58  Inferencing          : 0.16
% 3.33/1.58  Reduction            : 0.17
% 3.33/1.58  Demodulation         : 0.13
% 3.33/1.58  BG Simplification    : 0.03
% 3.33/1.58  Subsumption          : 0.07
% 3.33/1.58  Abstraction          : 0.02
% 3.33/1.58  MUC search           : 0.00
% 3.33/1.58  Cooper               : 0.00
% 3.33/1.58  Total                : 0.85
% 3.33/1.58  Index Insertion      : 0.00
% 3.33/1.58  Index Deletion       : 0.00
% 3.33/1.58  Index Matching       : 0.00
% 3.33/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
