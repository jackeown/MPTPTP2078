%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:34 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   83 (  93 expanded)
%              Number of leaves         :   42 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   77 (  92 expanded)
%              Number of equality atoms :   55 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_84,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_82,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_66,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1031,plain,(
    ! [A_154,B_155,C_156,D_157] : k2_xboole_0(k1_enumset1(A_154,B_155,C_156),k1_tarski(D_157)) = k2_enumset1(A_154,B_155,C_156,D_157) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1049,plain,(
    ! [A_36,B_37,D_157] : k2_xboole_0(k2_tarski(A_36,B_37),k1_tarski(D_157)) = k2_enumset1(A_36,A_36,B_37,D_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1031])).

tff(c_1062,plain,(
    ! [A_159,B_160,D_161] : k2_xboole_0(k2_tarski(A_159,B_160),k1_tarski(D_161)) = k1_enumset1(A_159,B_160,D_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1049])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_451,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_475,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_451])).

tff(c_480,plain,(
    ! [A_112] : k4_xboole_0(A_112,k1_xboole_0) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_475])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_486,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k3_xboole_0(A_112,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_14])).

tff(c_494,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_486])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_472,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_451])).

tff(c_610,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_472])).

tff(c_80,plain,(
    ! [A_66,B_67] : r1_tarski(k1_tarski(A_66),k2_tarski(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_86,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_241,plain,(
    ! [A_92,B_93] :
      ( k3_xboole_0(A_92,B_93) = A_92
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_254,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_241])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_304,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_tarski(A_100,B_101)
      | ~ r1_tarski(A_100,k3_xboole_0(B_101,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_736,plain,(
    ! [A_126,A_127,B_128] :
      ( r1_tarski(A_126,A_127)
      | ~ r1_tarski(A_126,k3_xboole_0(B_128,A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_304])).

tff(c_791,plain,(
    ! [A_134] :
      ( r1_tarski(A_134,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_134,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_736])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_984,plain,(
    ! [A_153] :
      ( k3_xboole_0(A_153,k2_tarski('#skF_7','#skF_8')) = A_153
      | ~ r1_tarski(A_153,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_791,c_10])).

tff(c_994,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_984])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1010,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_6])).

tff(c_1017,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_1010])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1025,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_18])).

tff(c_1029,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1025])).

tff(c_1068,plain,(
    k1_enumset1('#skF_7','#skF_8','#skF_5') = k2_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_1029])).

tff(c_22,plain,(
    ! [E_24,A_18,B_19] : r2_hidden(E_24,k1_enumset1(A_18,B_19,E_24)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1125,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_22])).

tff(c_44,plain,(
    ! [D_30,B_26,A_25] :
      ( D_30 = B_26
      | D_30 = A_25
      | ~ r2_hidden(D_30,k2_tarski(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1137,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1125,c_44])).

tff(c_1141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_82,c_1137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 17:06:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.53  
% 3.20/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.53  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.20/1.53  
% 3.20/1.53  %Foreground sorts:
% 3.20/1.53  
% 3.20/1.53  
% 3.20/1.53  %Background operators:
% 3.20/1.53  
% 3.20/1.53  
% 3.20/1.53  %Foreground operators:
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.20/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.20/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.20/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.20/1.53  
% 3.20/1.55  tff(f_101, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.20/1.55  tff(f_79, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.20/1.55  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.20/1.55  tff(f_73, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.20/1.55  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.20/1.55  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.20/1.55  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.20/1.55  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.20/1.55  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.20/1.55  tff(f_91, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.20/1.55  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.20/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.20/1.55  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.20/1.55  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.20/1.55  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.20/1.55  tff(f_71, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.20/1.55  tff(c_84, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.20/1.55  tff(c_82, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.20/1.55  tff(c_68, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.55  tff(c_66, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.55  tff(c_1031, plain, (![A_154, B_155, C_156, D_157]: (k2_xboole_0(k1_enumset1(A_154, B_155, C_156), k1_tarski(D_157))=k2_enumset1(A_154, B_155, C_156, D_157))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.20/1.55  tff(c_1049, plain, (![A_36, B_37, D_157]: (k2_xboole_0(k2_tarski(A_36, B_37), k1_tarski(D_157))=k2_enumset1(A_36, A_36, B_37, D_157))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1031])).
% 3.20/1.55  tff(c_1062, plain, (![A_159, B_160, D_161]: (k2_xboole_0(k2_tarski(A_159, B_160), k1_tarski(D_161))=k1_enumset1(A_159, B_160, D_161))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1049])).
% 3.20/1.55  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.55  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.55  tff(c_451, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.55  tff(c_475, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_451])).
% 3.20/1.55  tff(c_480, plain, (![A_112]: (k4_xboole_0(A_112, k1_xboole_0)=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_475])).
% 3.20/1.55  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.55  tff(c_486, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k3_xboole_0(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_480, c_14])).
% 3.20/1.55  tff(c_494, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_486])).
% 3.20/1.55  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.55  tff(c_472, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_451])).
% 3.20/1.55  tff(c_610, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_494, c_472])).
% 3.20/1.55  tff(c_80, plain, (![A_66, B_67]: (r1_tarski(k1_tarski(A_66), k2_tarski(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.20/1.55  tff(c_86, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.20/1.55  tff(c_241, plain, (![A_92, B_93]: (k3_xboole_0(A_92, B_93)=A_92 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.55  tff(c_254, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_86, c_241])).
% 3.20/1.55  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.55  tff(c_304, plain, (![A_100, B_101, C_102]: (r1_tarski(A_100, B_101) | ~r1_tarski(A_100, k3_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.55  tff(c_736, plain, (![A_126, A_127, B_128]: (r1_tarski(A_126, A_127) | ~r1_tarski(A_126, k3_xboole_0(B_128, A_127)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_304])).
% 3.20/1.55  tff(c_791, plain, (![A_134]: (r1_tarski(A_134, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_134, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_254, c_736])).
% 3.20/1.55  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.55  tff(c_984, plain, (![A_153]: (k3_xboole_0(A_153, k2_tarski('#skF_7', '#skF_8'))=A_153 | ~r1_tarski(A_153, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_791, c_10])).
% 3.20/1.55  tff(c_994, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_80, c_984])).
% 3.20/1.55  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.55  tff(c_1010, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_994, c_6])).
% 3.20/1.55  tff(c_1017, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_610, c_1010])).
% 3.20/1.55  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.55  tff(c_1025, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1017, c_18])).
% 3.20/1.55  tff(c_1029, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1025])).
% 3.20/1.55  tff(c_1068, plain, (k1_enumset1('#skF_7', '#skF_8', '#skF_5')=k2_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1062, c_1029])).
% 3.20/1.55  tff(c_22, plain, (![E_24, A_18, B_19]: (r2_hidden(E_24, k1_enumset1(A_18, B_19, E_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.55  tff(c_1125, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_22])).
% 3.20/1.55  tff(c_44, plain, (![D_30, B_26, A_25]: (D_30=B_26 | D_30=A_25 | ~r2_hidden(D_30, k2_tarski(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.55  tff(c_1137, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1125, c_44])).
% 3.20/1.55  tff(c_1141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_82, c_1137])).
% 3.20/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.55  
% 3.20/1.55  Inference rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Ref     : 0
% 3.20/1.55  #Sup     : 263
% 3.20/1.55  #Fact    : 0
% 3.20/1.55  #Define  : 0
% 3.20/1.55  #Split   : 0
% 3.20/1.55  #Chain   : 0
% 3.20/1.55  #Close   : 0
% 3.20/1.55  
% 3.20/1.55  Ordering : KBO
% 3.20/1.55  
% 3.20/1.55  Simplification rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Subsume      : 5
% 3.20/1.55  #Demod        : 149
% 3.20/1.55  #Tautology    : 199
% 3.20/1.55  #SimpNegUnit  : 1
% 3.20/1.55  #BackRed      : 1
% 3.20/1.55  
% 3.20/1.55  #Partial instantiations: 0
% 3.20/1.55  #Strategies tried      : 1
% 3.20/1.55  
% 3.20/1.55  Timing (in seconds)
% 3.20/1.55  ----------------------
% 3.20/1.55  Preprocessing        : 0.35
% 3.20/1.55  Parsing              : 0.18
% 3.20/1.55  CNF conversion       : 0.02
% 3.20/1.55  Main loop            : 0.36
% 3.20/1.55  Inferencing          : 0.12
% 3.20/1.55  Reduction            : 0.14
% 3.20/1.55  Demodulation         : 0.11
% 3.20/1.55  BG Simplification    : 0.02
% 3.20/1.55  Subsumption          : 0.06
% 3.20/1.55  Abstraction          : 0.02
% 3.20/1.55  MUC search           : 0.00
% 3.20/1.55  Cooper               : 0.00
% 3.20/1.55  Total                : 0.75
% 3.20/1.55  Index Insertion      : 0.00
% 3.20/1.55  Index Deletion       : 0.00
% 3.20/1.55  Index Matching       : 0.00
% 3.20/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
