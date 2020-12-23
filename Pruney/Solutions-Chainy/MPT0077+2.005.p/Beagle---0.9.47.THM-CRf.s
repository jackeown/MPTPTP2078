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
% DateTime   : Thu Dec  3 09:43:35 EST 2020

% Result     : Theorem 15.80s
% Output     : CNFRefutation 16.27s
% Verified   : 
% Statistics : Number of formulae       :  408 (2831 expanded)
%              Number of leaves         :   29 ( 975 expanded)
%              Depth                    :   24
%              Number of atoms          :  482 (3420 expanded)
%              Number of equality atoms :  321 (2462 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_77,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_43,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_642,plain,(
    ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_22,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_296,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),B_49) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_306,plain,(
    ! [A_48] : k4_xboole_0(A_48,k1_xboole_0) = k2_xboole_0(A_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_22])).

tff(c_322,plain,(
    ! [A_48] : k2_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_306])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_27] : r1_xboole_0(A_27,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_122,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,(
    ! [A_27] : k3_xboole_0(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_122])).

tff(c_226,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_241,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_244,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_241])).

tff(c_677,plain,(
    ! [A_74,B_75,C_76] : k4_xboole_0(k4_xboole_0(A_74,B_75),C_76) = k4_xboole_0(A_74,k2_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_720,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k2_xboole_0(B_75,k4_xboole_0(A_74,B_75))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_677])).

tff(c_745,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k2_xboole_0(B_75,A_74)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_720])).

tff(c_26,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_186,plain,(
    r1_xboole_0('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_190,plain,(
    k3_xboole_0('#skF_6','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_186,c_6])).

tff(c_28,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_437,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_466,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(k4_xboole_0(A_25,B_26),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_437])).

tff(c_4432,plain,(
    ! [A_187,B_188] : k2_xboole_0(k4_xboole_0(A_187,B_188),k3_xboole_0(A_187,B_188)) = k2_xboole_0(A_187,k4_xboole_0(A_187,B_188)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_466])).

tff(c_4614,plain,(
    k2_xboole_0(k4_xboole_0('#skF_6','#skF_8'),k1_xboole_0) = k2_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_4432])).

tff(c_4674,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_8')) = k4_xboole_0('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_4614])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_460,plain,(
    ! [B_21,A_20] : k2_xboole_0(B_21,k4_xboole_0(A_20,B_21)) = k2_xboole_0(B_21,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_437])).

tff(c_1369,plain,(
    ! [B_99,A_100] : k2_xboole_0(B_99,k2_xboole_0(A_100,B_99)) = k2_xboole_0(B_99,A_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_460])).

tff(c_1428,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1369])).

tff(c_315,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_296])).

tff(c_749,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k2_xboole_0(B_78,A_77)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_720])).

tff(c_767,plain,(
    ! [A_77,B_78] : k3_xboole_0(A_77,k2_xboole_0(B_78,A_77)) = k4_xboole_0(A_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_28])).

tff(c_799,plain,(
    ! [A_77,B_78] : k3_xboole_0(A_77,k2_xboole_0(B_78,A_77)) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_767])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_302,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),k4_xboole_0(A_48,B_49)) = k3_xboole_0(k2_xboole_0(A_48,B_49),B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_28])).

tff(c_321,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),k4_xboole_0(A_48,B_49)) = k3_xboole_0(B_49,k2_xboole_0(A_48,B_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_302])).

tff(c_3088,plain,(
    ! [A_156,B_157] : k4_xboole_0(k2_xboole_0(A_156,B_157),k4_xboole_0(A_156,B_157)) = B_157 ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_321])).

tff(c_3139,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(k2_xboole_0(A_1,B_2),A_1),k4_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_3088])).

tff(c_3192,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_2,c_3139])).

tff(c_5603,plain,(
    k4_xboole_0(k4_xboole_0('#skF_6','#skF_8'),k4_xboole_0(k4_xboole_0('#skF_6','#skF_8'),'#skF_6')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4674,c_3192])).

tff(c_5666,plain,(
    k4_xboole_0('#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_745,c_26,c_26,c_5603])).

tff(c_791,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_749])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_217,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_221,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_217,c_6])).

tff(c_4608,plain,(
    k2_xboole_0(k4_xboole_0('#skF_6','#skF_7'),k1_xboole_0) = k2_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_4432])).

tff(c_4672,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_7')) = k4_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_4608])).

tff(c_5008,plain,(
    k4_xboole_0(k4_xboole_0('#skF_6','#skF_7'),k4_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_6')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4672,c_3192])).

tff(c_5071,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_791,c_26,c_2,c_26,c_5008])).

tff(c_25771,plain,(
    ! [C_363] : k4_xboole_0('#skF_6',k2_xboole_0('#skF_7',C_363)) = k4_xboole_0('#skF_6',C_363) ),
    inference(superposition,[status(thm),theory(equality)],[c_5071,c_26])).

tff(c_512,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_538,plain,(
    ! [A_27,C_58] :
      ( ~ r1_xboole_0(A_27,k1_xboole_0)
      | ~ r2_hidden(C_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_512])).

tff(c_552,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_538])).

tff(c_447,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),k4_xboole_0(B_54,A_53)) = k4_xboole_0(A_53,k4_xboole_0(B_54,A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_24])).

tff(c_3533,plain,(
    ! [A_166,B_167] : k4_xboole_0(A_166,k4_xboole_0(B_167,A_166)) = A_166 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3192,c_447])).

tff(c_3565,plain,(
    ! [A_166,B_167] : k3_xboole_0(A_166,k4_xboole_0(B_167,A_166)) = k4_xboole_0(A_166,A_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_3533,c_28])).

tff(c_3658,plain,(
    ! [A_168,B_169] : k3_xboole_0(A_168,k4_xboole_0(B_169,A_168)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_3565])).

tff(c_918,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_2'(A_83,B_84),k3_xboole_0(A_83,B_84))
      | r1_xboole_0(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_951,plain,(
    ! [B_4,A_3] :
      ( r2_hidden('#skF_2'(B_4,A_3),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(B_4,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_918])).

tff(c_3669,plain,(
    ! [B_169,A_168] :
      ( r2_hidden('#skF_2'(k4_xboole_0(B_169,A_168),A_168),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(B_169,A_168),A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3658,c_951])).

tff(c_3757,plain,(
    ! [B_169,A_168] : r1_xboole_0(k4_xboole_0(B_169,A_168),A_168) ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_3669])).

tff(c_27736,plain,(
    ! [C_374] : r1_xboole_0(k4_xboole_0('#skF_6',C_374),k2_xboole_0('#skF_7',C_374)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25771,c_3757])).

tff(c_27834,plain,(
    r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5666,c_27736])).

tff(c_27907,plain,(
    r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_27834])).

tff(c_27909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_642,c_27907])).

tff(c_27911,plain,(
    r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_42,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_28096,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27911,c_44])).

tff(c_28097,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28096])).

tff(c_312,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_296])).

tff(c_27957,plain,(
    ! [A_377,B_378,C_379] : k4_xboole_0(k4_xboole_0(A_377,B_378),C_379) = k4_xboole_0(A_377,k2_xboole_0(B_378,C_379)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_31549,plain,(
    ! [C_463,A_464,B_465] : k2_xboole_0(C_463,k4_xboole_0(A_464,k2_xboole_0(B_465,C_463))) = k2_xboole_0(C_463,k4_xboole_0(A_464,B_465)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27957,c_20])).

tff(c_31719,plain,(
    ! [C_463,B_465] : k2_xboole_0(C_463,k4_xboole_0(k2_xboole_0(B_465,C_463),B_465)) = k2_xboole_0(C_463,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_31549])).

tff(c_31771,plain,(
    ! [C_466,B_467] : k2_xboole_0(C_466,k4_xboole_0(C_466,B_467)) = C_466 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_322,c_31719])).

tff(c_28000,plain,(
    ! [A_377,B_378] : k4_xboole_0(A_377,k2_xboole_0(B_378,k4_xboole_0(A_377,B_378))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_27957])).

tff(c_28038,plain,(
    ! [A_380,B_381] : k4_xboole_0(A_380,k2_xboole_0(B_381,A_380)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28000])).

tff(c_28056,plain,(
    ! [A_380,B_381] : k3_xboole_0(A_380,k2_xboole_0(B_381,A_380)) = k4_xboole_0(A_380,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28038,c_28])).

tff(c_28088,plain,(
    ! [A_380,B_381] : k3_xboole_0(A_380,k2_xboole_0(B_381,A_380)) = A_380 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28056])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_241])).

tff(c_250,plain,(
    ! [A_44] : k4_xboole_0(A_44,k1_xboole_0) = k3_xboole_0(A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_28])).

tff(c_262,plain,(
    ! [A_44] : k3_xboole_0(A_44,A_44) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_250])).

tff(c_574,plain,(
    ! [A_61,C_62] :
      ( ~ r1_xboole_0(A_61,A_61)
      | ~ r2_hidden(C_62,A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_512])).

tff(c_580,plain,(
    ! [C_62,B_6] :
      ( ~ r2_hidden(C_62,B_6)
      | k3_xboole_0(B_6,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_574])).

tff(c_605,plain,(
    ! [C_66,B_67] :
      ( ~ r2_hidden(C_66,B_67)
      | k1_xboole_0 != B_67 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_580])).

tff(c_630,plain,(
    ! [B_70,A_71] :
      ( k1_xboole_0 != B_70
      | r1_xboole_0(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_12,c_605])).

tff(c_28545,plain,(
    ! [A_398,B_399] :
      ( k3_xboole_0(A_398,B_399) = k1_xboole_0
      | k1_xboole_0 != B_399 ) ),
    inference(resolution,[status(thm)],[c_630,c_6])).

tff(c_28608,plain,(
    ! [A_380,B_381] :
      ( k1_xboole_0 = A_380
      | k2_xboole_0(B_381,A_380) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28088,c_28545])).

tff(c_34888,plain,(
    ! [C_503,B_504] :
      ( k4_xboole_0(C_503,B_504) = k1_xboole_0
      | k1_xboole_0 != C_503 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31771,c_28608])).

tff(c_35026,plain,(
    ! [B_504,C_503] :
      ( k2_xboole_0(B_504,k1_xboole_0) = k2_xboole_0(B_504,C_503)
      | k1_xboole_0 != C_503 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34888,c_20])).

tff(c_35699,plain,(
    ! [B_504] : k2_xboole_0(B_504,k1_xboole_0) = B_504 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_35026])).

tff(c_32883,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),k4_xboole_0(A_48,B_49)) = B_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28088,c_321])).

tff(c_34938,plain,(
    ! [C_503,B_504] :
      ( k4_xboole_0(k2_xboole_0(C_503,B_504),k1_xboole_0) = B_504
      | k1_xboole_0 != C_503 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34888,c_32883])).

tff(c_35988,plain,(
    ! [B_504] : k2_xboole_0(k1_xboole_0,B_504) = B_504 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_34938])).

tff(c_31766,plain,(
    ! [C_463,B_465] : k2_xboole_0(C_463,k4_xboole_0(C_463,B_465)) = C_463 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_322,c_31719])).

tff(c_27910,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_27918,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27910,c_6])).

tff(c_477,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(A_25,k4_xboole_0(A_25,B_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_466])).

tff(c_36742,plain,(
    ! [A_520,B_521] : k2_xboole_0(k4_xboole_0(A_520,B_521),k3_xboole_0(A_520,B_521)) = A_520 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31766,c_477])).

tff(c_36964,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_27918,c_36742])).

tff(c_29192,plain,(
    ! [B_420,A_421] : k2_xboole_0(B_420,k2_xboole_0(A_421,B_420)) = k2_xboole_0(B_420,A_421) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_460])).

tff(c_29251,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_29192])).

tff(c_37383,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36964,c_29251])).

tff(c_37465,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35988,c_31766,c_2,c_2,c_37383])).

tff(c_28025,plain,(
    ! [A_377,B_378] : k4_xboole_0(A_377,k2_xboole_0(B_378,A_377)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28000])).

tff(c_31848,plain,(
    ! [C_466,B_467] : k4_xboole_0(k4_xboole_0(C_466,B_467),C_466) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31771,c_28025])).

tff(c_27973,plain,(
    ! [A_377,B_378,C_379] : k4_xboole_0(k4_xboole_0(A_377,B_378),k4_xboole_0(A_377,k2_xboole_0(B_378,C_379))) = k3_xboole_0(k4_xboole_0(A_377,B_378),C_379) ),
    inference(superposition,[status(thm),theory(equality)],[c_27957,c_28])).

tff(c_37504,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_37465,c_27973])).

tff(c_37573,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31848,c_4,c_37504])).

tff(c_28178,plain,(
    ! [A_384,B_385] :
      ( r2_hidden('#skF_2'(A_384,B_385),k3_xboole_0(A_384,B_385))
      | r1_xboole_0(A_384,B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28214,plain,(
    ! [B_4,A_3] :
      ( r2_hidden('#skF_2'(B_4,A_3),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(B_4,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_28178])).

tff(c_37616,plain,
    ( r2_hidden('#skF_2'(k4_xboole_0('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0)
    | r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_37573,c_28214])).

tff(c_37675,plain,(
    r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_37616])).

tff(c_37707,plain,(
    k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37675,c_6])).

tff(c_35187,plain,(
    ! [A_505,B_506,C_507] : k4_xboole_0(k4_xboole_0(A_505,B_506),k4_xboole_0(A_505,k2_xboole_0(B_506,C_507))) = k3_xboole_0(k4_xboole_0(A_505,B_506),C_507) ),
    inference(superposition,[status(thm),theory(equality)],[c_27957,c_28])).

tff(c_35427,plain,(
    ! [B_506,C_507] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_506,C_507),B_506),k1_xboole_0) = k3_xboole_0(k4_xboole_0(k2_xboole_0(B_506,C_507),B_506),C_507) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_35187])).

tff(c_35504,plain,(
    ! [C_507,B_506] : k3_xboole_0(C_507,k4_xboole_0(C_507,B_506)) = k4_xboole_0(C_507,B_506) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_4,c_312,c_22,c_35427])).

tff(c_229,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,k4_xboole_0(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_28])).

tff(c_37709,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35504,c_229])).

tff(c_38347,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_37707,c_37709])).

tff(c_38434,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35699,c_37465,c_26,c_26,c_38347])).

tff(c_33228,plain,(
    ! [A_484,B_485] : k4_xboole_0(k2_xboole_0(A_484,B_485),k4_xboole_0(B_485,A_484)) = k4_xboole_0(A_484,k4_xboole_0(B_485,A_484)) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_24])).

tff(c_33377,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),k4_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_33228])).

tff(c_33475,plain,(
    ! [A_486,B_487] : k4_xboole_0(A_486,k4_xboole_0(B_487,A_486)) = A_486 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32883,c_33377])).

tff(c_33513,plain,(
    ! [A_486,B_487] : k3_xboole_0(A_486,k4_xboole_0(B_487,A_486)) = k4_xboole_0(A_486,A_486) ),
    inference(superposition,[status(thm),theory(equality)],[c_33475,c_28])).

tff(c_33646,plain,(
    ! [A_488,B_489] : k3_xboole_0(A_488,k4_xboole_0(B_489,A_488)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_33513])).

tff(c_33663,plain,(
    ! [B_489,A_488] :
      ( r2_hidden('#skF_2'(k4_xboole_0(B_489,A_488),A_488),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(B_489,A_488),A_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33646,c_28214])).

tff(c_33786,plain,(
    ! [B_489,A_488] : r1_xboole_0(k4_xboole_0(B_489,A_488),A_488) ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_33663])).

tff(c_38499,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38434,c_33786])).

tff(c_38546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28097,c_38499])).

tff(c_38547,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_28096])).

tff(c_38560,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_38547])).

tff(c_41778,plain,(
    ! [C_622,A_623,B_624] : k2_xboole_0(C_622,k4_xboole_0(A_623,k2_xboole_0(B_624,C_622))) = k2_xboole_0(C_622,k4_xboole_0(A_623,B_624)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27957,c_20])).

tff(c_41923,plain,(
    ! [C_622,B_624] : k2_xboole_0(C_622,k4_xboole_0(k2_xboole_0(B_624,C_622),B_624)) = k2_xboole_0(C_622,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_41778])).

tff(c_41960,plain,(
    ! [C_622,B_624] : k2_xboole_0(C_622,k4_xboole_0(C_622,B_624)) = C_622 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_322,c_41923])).

tff(c_38548,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28096])).

tff(c_38567,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38548,c_6])).

tff(c_40939,plain,(
    ! [A_602,B_603] : k4_xboole_0(A_602,k3_xboole_0(A_602,B_603)) = k3_xboole_0(A_602,k4_xboole_0(A_602,B_603)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_28])).

tff(c_40995,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38567,c_40939])).

tff(c_41042,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_40995])).

tff(c_41963,plain,(
    ! [C_625,B_626] : k2_xboole_0(C_625,k4_xboole_0(C_625,B_626)) = C_625 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_322,c_41923])).

tff(c_42196,plain,(
    ! [A_627,B_628] : k2_xboole_0(A_627,k3_xboole_0(A_627,B_628)) = A_627 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_41963])).

tff(c_42826,plain,(
    ! [A_636,B_637] : k2_xboole_0(A_636,k3_xboole_0(B_637,A_636)) = A_636 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42196])).

tff(c_42875,plain,(
    ! [B_637,A_636] : k4_xboole_0(k3_xboole_0(B_637,A_636),A_636) = k4_xboole_0(A_636,A_636) ),
    inference(superposition,[status(thm),theory(equality)],[c_42826,c_312])).

tff(c_43314,plain,(
    ! [B_642,A_643] : k4_xboole_0(k3_xboole_0(B_642,A_643),A_643) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_42875])).

tff(c_43365,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41042,c_43314])).

tff(c_42499,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),k4_xboole_0(A_48,B_49)) = B_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28088,c_321])).

tff(c_44999,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')),k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_43365,c_42499])).

tff(c_45035,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_41960,c_44999])).

tff(c_42030,plain,(
    ! [C_625,B_626] : k4_xboole_0(k4_xboole_0(C_625,B_626),C_625) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41963,c_28025])).

tff(c_39130,plain,(
    ! [A_544,B_545] :
      ( k3_xboole_0(A_544,B_545) = k1_xboole_0
      | k1_xboole_0 != B_545 ) ),
    inference(resolution,[status(thm)],[c_630,c_6])).

tff(c_39153,plain,(
    ! [A_544,B_381] :
      ( k1_xboole_0 = A_544
      | k2_xboole_0(B_381,A_544) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39130,c_28088])).

tff(c_45512,plain,(
    ! [C_666,B_667] :
      ( k4_xboole_0(C_666,B_667) = k1_xboole_0
      | k1_xboole_0 != C_666 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41963,c_39153])).

tff(c_45591,plain,(
    ! [C_666,B_667] :
      ( k4_xboole_0(k2_xboole_0(C_666,B_667),k1_xboole_0) = B_667
      | k1_xboole_0 != C_666 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45512,c_42499])).

tff(c_46732,plain,(
    ! [B_667] : k2_xboole_0(k1_xboole_0,B_667) = B_667 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_45591])).

tff(c_47945,plain,(
    ! [A_685,B_686] : k2_xboole_0(k4_xboole_0(A_685,B_686),k3_xboole_0(A_685,B_686)) = A_685 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41960,c_477])).

tff(c_48193,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_27918,c_47945])).

tff(c_39531,plain,(
    ! [B_555,A_556] : k4_xboole_0(k2_xboole_0(B_555,A_556),B_555) = k4_xboole_0(A_556,B_555) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_296])).

tff(c_39540,plain,(
    ! [B_555,A_556] : k2_xboole_0(B_555,k4_xboole_0(A_556,B_555)) = k2_xboole_0(B_555,k2_xboole_0(B_555,A_556)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39531,c_20])).

tff(c_39586,plain,(
    ! [B_555,A_556] : k2_xboole_0(B_555,k2_xboole_0(B_555,A_556)) = k2_xboole_0(B_555,A_556) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_39540])).

tff(c_48478,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48193,c_39586])).

tff(c_48562,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46732,c_41960,c_2,c_2,c_48478])).

tff(c_48602,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48562,c_27973])).

tff(c_48674,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_45035,c_42030,c_4,c_48602])).

tff(c_48676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38560,c_48674])).

tff(c_48678,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48875,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48678,c_38])).

tff(c_48876,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48875])).

tff(c_48677,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_48686,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48677,c_6])).

tff(c_48691,plain,(
    ! [A_690,B_691] : k4_xboole_0(k2_xboole_0(A_690,B_691),B_691) = k4_xboole_0(A_690,B_691) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48707,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48691])).

tff(c_48698,plain,(
    ! [A_690] : k4_xboole_0(A_690,k1_xboole_0) = k2_xboole_0(A_690,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48691,c_22])).

tff(c_48713,plain,(
    ! [A_690] : k2_xboole_0(A_690,k1_xboole_0) = A_690 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_48698])).

tff(c_48805,plain,(
    ! [A_695,B_696] : k4_xboole_0(A_695,k4_xboole_0(A_695,B_696)) = k3_xboole_0(A_695,B_696) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48829,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_48805])).

tff(c_48834,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_48829])).

tff(c_49464,plain,(
    ! [A_734,B_735,C_736] : k4_xboole_0(k4_xboole_0(A_734,B_735),C_736) = k4_xboole_0(A_734,k2_xboole_0(B_735,C_736)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_51982,plain,(
    ! [C_815,A_816,B_817] : k2_xboole_0(C_815,k4_xboole_0(A_816,k2_xboole_0(B_817,C_815))) = k2_xboole_0(C_815,k4_xboole_0(A_816,B_817)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49464,c_20])).

tff(c_52078,plain,(
    ! [C_815,B_817] : k2_xboole_0(C_815,k4_xboole_0(k2_xboole_0(B_817,C_815),B_817)) = k2_xboole_0(C_815,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48834,c_51982])).

tff(c_52117,plain,(
    ! [C_815,B_817] : k2_xboole_0(C_815,k4_xboole_0(C_815,B_817)) = C_815 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48707,c_48713,c_52078])).

tff(c_48975,plain,(
    ! [A_704,B_705] : k2_xboole_0(A_704,k4_xboole_0(B_705,A_704)) = k2_xboole_0(A_704,B_705) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48997,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(k4_xboole_0(A_25,B_26),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_48975])).

tff(c_49013,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(A_25,k4_xboole_0(A_25,B_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48997])).

tff(c_55289,plain,(
    ! [A_852,B_853] : k2_xboole_0(k4_xboole_0(A_852,B_853),k3_xboole_0(A_852,B_853)) = A_852 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52117,c_49013])).

tff(c_55466,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_48686,c_55289])).

tff(c_52122,plain,(
    ! [C_818,B_819] : k2_xboole_0(C_818,k4_xboole_0(C_818,B_819)) = C_818 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48707,c_48713,c_52078])).

tff(c_49477,plain,(
    ! [A_734,B_735] : k4_xboole_0(A_734,k2_xboole_0(B_735,k4_xboole_0(A_734,B_735))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_49464,c_48834])).

tff(c_49540,plain,(
    ! [A_737,B_738] : k4_xboole_0(A_737,k2_xboole_0(B_738,A_737)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_49477])).

tff(c_49558,plain,(
    ! [A_737,B_738] : k3_xboole_0(A_737,k2_xboole_0(B_738,A_737)) = k4_xboole_0(A_737,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_49540,c_28])).

tff(c_49687,plain,(
    ! [A_742,B_743] : k3_xboole_0(A_742,k2_xboole_0(B_743,A_742)) = A_742 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_49558])).

tff(c_48883,plain,(
    ! [A_701] : k4_xboole_0(A_701,A_701) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_48829])).

tff(c_48888,plain,(
    ! [A_701] : k4_xboole_0(A_701,k1_xboole_0) = k3_xboole_0(A_701,A_701) ),
    inference(superposition,[status(thm),theory(equality)],[c_48883,c_28])).

tff(c_48900,plain,(
    ! [A_701] : k3_xboole_0(A_701,A_701) = A_701 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_48888])).

tff(c_48904,plain,(
    ! [A_702] : k3_xboole_0(A_702,A_702) = A_702 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_48888])).

tff(c_18,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_49050,plain,(
    ! [A_707,C_708] :
      ( ~ r1_xboole_0(A_707,A_707)
      | ~ r2_hidden(C_708,A_707) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48904,c_18])).

tff(c_49053,plain,(
    ! [C_708,B_6] :
      ( ~ r2_hidden(C_708,B_6)
      | k3_xboole_0(B_6,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_49050])).

tff(c_49062,plain,(
    ! [C_709,B_710] :
      ( ~ r2_hidden(C_709,B_710)
      | k1_xboole_0 != B_710 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48900,c_49053])).

tff(c_49069,plain,(
    ! [B_711,A_712] :
      ( k1_xboole_0 != B_711
      | r1_xboole_0(A_712,B_711) ) ),
    inference(resolution,[status(thm)],[c_12,c_49062])).

tff(c_49085,plain,(
    ! [A_712,B_711] :
      ( k3_xboole_0(A_712,B_711) = k1_xboole_0
      | k1_xboole_0 != B_711 ) ),
    inference(resolution,[status(thm)],[c_49069,c_6])).

tff(c_49699,plain,(
    ! [A_742,B_743] :
      ( k1_xboole_0 = A_742
      | k2_xboole_0(B_743,A_742) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49687,c_49085])).

tff(c_53814,plain,(
    ! [C_837,B_838] :
      ( k4_xboole_0(C_837,B_838) = k1_xboole_0
      | k1_xboole_0 != C_837 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52122,c_49699])).

tff(c_53932,plain,(
    ! [B_838,C_837] :
      ( k2_xboole_0(B_838,k1_xboole_0) = k2_xboole_0(B_838,C_837)
      | k1_xboole_0 != C_837 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53814,c_20])).

tff(c_54036,plain,(
    ! [B_838,C_837] :
      ( k2_xboole_0(B_838,C_837) = B_838
      | k1_xboole_0 != C_837 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48713,c_53932])).

tff(c_55864,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_55466,c_54036])).

tff(c_48835,plain,(
    ! [A_697,B_698,C_699] :
      ( ~ r1_xboole_0(A_697,B_698)
      | ~ r2_hidden(C_699,k3_xboole_0(A_697,B_698)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48854,plain,(
    ! [A_27,C_699] :
      ( ~ r1_xboole_0(A_27,k1_xboole_0)
      | ~ r2_hidden(C_699,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_48835])).

tff(c_48867,plain,(
    ! [C_699] : ~ r2_hidden(C_699,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_48854])).

tff(c_49346,plain,(
    ! [A_730,B_731] : k4_xboole_0(k2_xboole_0(A_730,B_731),A_730) = k4_xboole_0(B_731,A_730) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48691])).

tff(c_49372,plain,(
    ! [B_18,A_17] : k4_xboole_0(k4_xboole_0(B_18,A_17),A_17) = k4_xboole_0(k2_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_49346])).

tff(c_50437,plain,(
    ! [B_779,A_780] : k4_xboole_0(k4_xboole_0(B_779,A_780),A_780) = k4_xboole_0(B_779,A_780) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48707,c_49372])).

tff(c_50455,plain,(
    ! [B_779,A_780] : k4_xboole_0(k4_xboole_0(B_779,A_780),k4_xboole_0(B_779,A_780)) = k3_xboole_0(k4_xboole_0(B_779,A_780),A_780) ),
    inference(superposition,[status(thm),theory(equality)],[c_50437,c_28])).

tff(c_50506,plain,(
    ! [A_780,B_779] : k3_xboole_0(A_780,k4_xboole_0(B_779,A_780)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48834,c_4,c_50455])).

tff(c_49807,plain,(
    ! [A_746,B_747] :
      ( r2_hidden('#skF_2'(A_746,B_747),k3_xboole_0(A_746,B_747))
      | r1_xboole_0(A_746,B_747) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50659,plain,(
    ! [B_785,A_786] :
      ( r2_hidden('#skF_2'(B_785,A_786),k3_xboole_0(A_786,B_785))
      | r1_xboole_0(B_785,A_786) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_49807])).

tff(c_50673,plain,(
    ! [B_779,A_780] :
      ( r2_hidden('#skF_2'(k4_xboole_0(B_779,A_780),A_780),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(B_779,A_780),A_780) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50506,c_50659])).

tff(c_50722,plain,(
    ! [B_787,A_788] : r1_xboole_0(k4_xboole_0(B_787,A_788),A_788) ),
    inference(negUnitSimplification,[status(thm)],[c_48867,c_50673])).

tff(c_51073,plain,(
    ! [A_797,B_798,C_799] : r1_xboole_0(k4_xboole_0(A_797,k2_xboole_0(B_798,C_799)),C_799) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_50722])).

tff(c_51132,plain,(
    ! [A_797,A_1,B_2] : r1_xboole_0(k4_xboole_0(A_797,k2_xboole_0(A_1,B_2)),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51073])).

tff(c_56178,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_55864,c_51132])).

tff(c_56247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48876,c_56178])).

tff(c_56248,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48875])).

tff(c_56936,plain,(
    ! [A_892,B_893,C_894] : k4_xboole_0(k4_xboole_0(A_892,B_893),C_894) = k4_xboole_0(A_892,k2_xboole_0(B_893,C_894)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_62303,plain,(
    ! [C_1002,A_1003,B_1004] : k2_xboole_0(C_1002,k4_xboole_0(A_1003,k2_xboole_0(B_1004,C_1002))) = k2_xboole_0(C_1002,k4_xboole_0(A_1003,B_1004)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56936,c_20])).

tff(c_62462,plain,(
    ! [C_1002,B_1004] : k2_xboole_0(C_1002,k4_xboole_0(k2_xboole_0(B_1004,C_1002),B_1004)) = k2_xboole_0(C_1002,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48834,c_62303])).

tff(c_62518,plain,(
    ! [C_1002,B_1004] : k2_xboole_0(C_1002,k4_xboole_0(C_1002,B_1004)) = C_1002 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48707,c_48713,c_62462])).

tff(c_56280,plain,(
    ! [A_859,B_860] : k2_xboole_0(A_859,k4_xboole_0(B_860,A_859)) = k2_xboole_0(A_859,B_860) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56299,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(k4_xboole_0(A_25,B_26),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_56280])).

tff(c_60233,plain,(
    ! [A_975,B_976] : k2_xboole_0(k4_xboole_0(A_975,B_976),k3_xboole_0(A_975,B_976)) = k2_xboole_0(A_975,k4_xboole_0(A_975,B_976)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56299])).

tff(c_60392,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_xboole_0) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_48686,c_60233])).

tff(c_60455,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48713,c_60392])).

tff(c_62523,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62518,c_60455])).

tff(c_56949,plain,(
    ! [A_892,B_893] : k4_xboole_0(A_892,k2_xboole_0(B_893,k4_xboole_0(A_892,B_893))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_56936,c_48834])).

tff(c_57008,plain,(
    ! [A_895,B_896] : k4_xboole_0(A_895,k2_xboole_0(B_896,A_895)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56949])).

tff(c_57093,plain,(
    ! [B_900,A_901] : k4_xboole_0(B_900,k2_xboole_0(B_900,A_901)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_57008])).

tff(c_57114,plain,(
    ! [B_900,A_901] : k3_xboole_0(B_900,k2_xboole_0(B_900,A_901)) = k4_xboole_0(B_900,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_57093,c_28])).

tff(c_57153,plain,(
    ! [B_900,A_901] : k3_xboole_0(B_900,k2_xboole_0(B_900,A_901)) = B_900 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_57114])).

tff(c_56306,plain,(
    ! [B_21,A_20] : k2_xboole_0(B_21,k4_xboole_0(A_20,B_21)) = k2_xboole_0(B_21,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_56280])).

tff(c_56830,plain,(
    ! [B_887,A_888] : k2_xboole_0(B_887,k2_xboole_0(A_888,B_887)) = k2_xboole_0(B_887,A_888) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56306])).

tff(c_56871,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56830])).

tff(c_59582,plain,(
    ! [A_965,B_966] : k4_xboole_0(k2_xboole_0(A_965,B_966),k4_xboole_0(B_966,A_965)) = k4_xboole_0(A_965,k4_xboole_0(B_966,A_965)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56280,c_24])).

tff(c_59642,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k4_xboole_0(k2_xboole_0(A_1,B_2),A_1)) = k4_xboole_0(A_1,k4_xboole_0(k2_xboole_0(A_1,B_2),A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56871,c_59582])).

tff(c_59724,plain,(
    ! [A_967,B_968] : k4_xboole_0(A_967,k4_xboole_0(B_968,A_967)) = A_967 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48707,c_57153,c_4,c_28,c_59642])).

tff(c_59753,plain,(
    ! [A_967,B_968] : k3_xboole_0(A_967,k4_xboole_0(B_968,A_967)) = k4_xboole_0(A_967,A_967) ),
    inference(superposition,[status(thm),theory(equality)],[c_59724,c_28])).

tff(c_59847,plain,(
    ! [A_969,B_970] : k3_xboole_0(A_969,k4_xboole_0(B_970,A_969)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48834,c_59753])).

tff(c_56754,plain,(
    ! [A_884,B_885] :
      ( r2_hidden('#skF_2'(A_884,B_885),k3_xboole_0(A_884,B_885))
      | r1_xboole_0(A_884,B_885) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56787,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4),k3_xboole_0(B_4,A_3))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_56754])).

tff(c_59867,plain,(
    ! [B_970,A_969] :
      ( r2_hidden('#skF_2'(k4_xboole_0(B_970,A_969),A_969),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(B_970,A_969),A_969) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59847,c_56787])).

tff(c_60103,plain,(
    ! [B_973,A_974] : r1_xboole_0(k4_xboole_0(B_973,A_974),A_974) ),
    inference(negUnitSimplification,[status(thm)],[c_48867,c_59867])).

tff(c_60149,plain,(
    ! [A_22,B_23,C_24] : r1_xboole_0(k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)),C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_60103])).

tff(c_62850,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_62523,c_60149])).

tff(c_62890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56248,c_62850])).

tff(c_62892,plain,(
    ~ r1_xboole_0('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62923,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62892,c_34])).

tff(c_62924,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62923])).

tff(c_62930,plain,(
    ! [A_1011,B_1012] : k4_xboole_0(k2_xboole_0(A_1011,B_1012),B_1012) = k4_xboole_0(A_1011,B_1012) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62940,plain,(
    ! [A_1011] : k4_xboole_0(A_1011,k1_xboole_0) = k2_xboole_0(A_1011,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62930,c_22])).

tff(c_62959,plain,(
    ! [A_1011] : k2_xboole_0(A_1011,k1_xboole_0) = A_1011 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62940])).

tff(c_62952,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_62930])).

tff(c_62990,plain,(
    ! [A_1014,B_1015] : k4_xboole_0(A_1014,k4_xboole_0(A_1014,B_1015)) = k3_xboole_0(A_1014,B_1015) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63011,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_62990])).

tff(c_63016,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_63011])).

tff(c_63618,plain,(
    ! [A_1053,B_1054,C_1055] : k4_xboole_0(k4_xboole_0(A_1053,B_1054),C_1055) = k4_xboole_0(A_1053,k2_xboole_0(B_1054,C_1055)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70021,plain,(
    ! [C_1205,A_1206,B_1207] : k2_xboole_0(C_1205,k4_xboole_0(A_1206,k2_xboole_0(B_1207,C_1205))) = k2_xboole_0(C_1205,k4_xboole_0(A_1206,B_1207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63618,c_20])).

tff(c_70256,plain,(
    ! [C_1205,B_1207] : k2_xboole_0(C_1205,k4_xboole_0(k2_xboole_0(B_1207,C_1205),B_1207)) = k2_xboole_0(C_1205,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_63016,c_70021])).

tff(c_70327,plain,(
    ! [C_1208,B_1209] : k2_xboole_0(C_1208,k4_xboole_0(C_1208,B_1209)) = C_1208 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62952,c_62959,c_70256])).

tff(c_63017,plain,(
    ! [A_1016] : k4_xboole_0(A_1016,A_1016) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_63011])).

tff(c_63022,plain,(
    ! [A_1016] : k4_xboole_0(A_1016,k1_xboole_0) = k3_xboole_0(A_1016,A_1016) ),
    inference(superposition,[status(thm),theory(equality)],[c_63017,c_28])).

tff(c_63037,plain,(
    ! [A_1016] : k3_xboole_0(A_1016,A_1016) = A_1016 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63022])).

tff(c_63202,plain,(
    ! [A_1023,B_1024,C_1025] :
      ( ~ r1_xboole_0(A_1023,B_1024)
      | ~ r2_hidden(C_1025,k3_xboole_0(A_1023,B_1024)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_63254,plain,(
    ! [A_1028,C_1029] :
      ( ~ r1_xboole_0(A_1028,A_1028)
      | ~ r2_hidden(C_1029,A_1028) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63037,c_63202])).

tff(c_63260,plain,(
    ! [C_1029,B_6] :
      ( ~ r2_hidden(C_1029,B_6)
      | k3_xboole_0(B_6,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_63254])).

tff(c_63269,plain,(
    ! [C_1030,B_1031] :
      ( ~ r2_hidden(C_1030,B_1031)
      | k1_xboole_0 != B_1031 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63037,c_63260])).

tff(c_63312,plain,(
    ! [B_1037,A_1038] :
      ( k1_xboole_0 != B_1037
      | r1_xboole_0(A_1038,B_1037) ) ),
    inference(resolution,[status(thm)],[c_12,c_63269])).

tff(c_63331,plain,(
    ! [A_1038,B_1037] :
      ( k3_xboole_0(A_1038,B_1037) = k1_xboole_0
      | k1_xboole_0 != B_1037 ) ),
    inference(resolution,[status(thm)],[c_63312,c_6])).

tff(c_63628,plain,(
    ! [A_1053,B_1054] : k4_xboole_0(A_1053,k2_xboole_0(B_1054,k4_xboole_0(A_1053,B_1054))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63618,c_63016])).

tff(c_63690,plain,(
    ! [A_1056,B_1057] : k4_xboole_0(A_1056,k2_xboole_0(B_1057,A_1056)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_63628])).

tff(c_63705,plain,(
    ! [A_1056,B_1057] : k3_xboole_0(A_1056,k2_xboole_0(B_1057,A_1056)) = k4_xboole_0(A_1056,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_63690,c_28])).

tff(c_63747,plain,(
    ! [A_1058,B_1059] : k3_xboole_0(A_1058,k2_xboole_0(B_1059,A_1058)) = A_1058 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63705])).

tff(c_63772,plain,(
    ! [A_1038,B_1059] :
      ( k1_xboole_0 = A_1038
      | k2_xboole_0(B_1059,A_1038) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63331,c_63747])).

tff(c_71949,plain,(
    ! [C_1220,B_1221] :
      ( k4_xboole_0(C_1220,B_1221) = k1_xboole_0
      | k1_xboole_0 != C_1220 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70327,c_63772])).

tff(c_72114,plain,(
    ! [B_1221,C_1220] :
      ( k2_xboole_0(B_1221,k1_xboole_0) = k2_xboole_0(B_1221,C_1220)
      | k1_xboole_0 != C_1220 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71949,c_20])).

tff(c_72429,plain,(
    ! [B_1221] : k2_xboole_0(B_1221,k1_xboole_0) = B_1221 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62959,c_72114])).

tff(c_62962,plain,(
    ! [A_1013] : k2_xboole_0(A_1013,k1_xboole_0) = A_1013 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62940])).

tff(c_62974,plain,(
    ! [A_1013] : k2_xboole_0(k1_xboole_0,A_1013) = A_1013 ),
    inference(superposition,[status(thm),theory(equality)],[c_62962,c_2])).

tff(c_63732,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_63690])).

tff(c_62891,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_62903,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62891,c_6])).

tff(c_62999,plain,(
    ! [A_1014,B_1015] : k2_xboole_0(k4_xboole_0(A_1014,B_1015),k3_xboole_0(A_1014,B_1015)) = k2_xboole_0(k4_xboole_0(A_1014,B_1015),A_1014) ),
    inference(superposition,[status(thm),theory(equality)],[c_62990,c_20])).

tff(c_69077,plain,(
    ! [A_1199,B_1200] : k2_xboole_0(k4_xboole_0(A_1199,B_1200),k3_xboole_0(A_1199,B_1200)) = k2_xboole_0(A_1199,k4_xboole_0(A_1199,B_1200)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62999])).

tff(c_69297,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_xboole_0) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_62903,c_69077])).

tff(c_69363,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62959,c_69297])).

tff(c_63791,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_63747])).

tff(c_64135,plain,(
    ! [A_1077,B_1078] : k4_xboole_0(k2_xboole_0(A_1077,B_1078),A_1077) = k4_xboole_0(B_1078,A_1077) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_62930])).

tff(c_64144,plain,(
    ! [A_1077,B_1078] : k4_xboole_0(k2_xboole_0(A_1077,B_1078),k4_xboole_0(B_1078,A_1077)) = k3_xboole_0(k2_xboole_0(A_1077,B_1078),A_1077) ),
    inference(superposition,[status(thm),theory(equality)],[c_64135,c_28])).

tff(c_64190,plain,(
    ! [A_1077,B_1078] : k4_xboole_0(k2_xboole_0(A_1077,B_1078),k4_xboole_0(B_1078,A_1077)) = A_1077 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63791,c_4,c_64144])).

tff(c_69632,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k4_xboole_0(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')),'#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_69363,c_64190])).

tff(c_69711,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62974,c_2,c_63732,c_26,c_2,c_26,c_69632])).

tff(c_70432,plain,(
    ! [C_1208,B_1209] : k4_xboole_0(k4_xboole_0(C_1208,B_1209),C_1208) = k4_xboole_0(C_1208,C_1208) ),
    inference(superposition,[status(thm),theory(equality)],[c_70327,c_62952])).

tff(c_70573,plain,(
    ! [C_1208,B_1209] : k4_xboole_0(k4_xboole_0(C_1208,B_1209),C_1208) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63016,c_70432])).

tff(c_71073,plain,(
    ! [A_1214,B_1215,C_1216] : k4_xboole_0(k4_xboole_0(A_1214,B_1215),k4_xboole_0(A_1214,k2_xboole_0(B_1215,C_1216))) = k3_xboole_0(k4_xboole_0(A_1214,B_1215),C_1216) ),
    inference(superposition,[status(thm),theory(equality)],[c_63618,c_28])).

tff(c_71158,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_69711,c_71073])).

tff(c_71355,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70573,c_4,c_71158])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_2'(A_12,B_13),k3_xboole_0(A_12,B_13))
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_63488,plain,(
    ! [B_1046,A_1047,C_1048] :
      ( ~ r1_xboole_0(B_1046,A_1047)
      | ~ r2_hidden(C_1048,k3_xboole_0(A_1047,B_1046)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_63202])).

tff(c_63521,plain,(
    ! [B_1049,A_1050] :
      ( ~ r1_xboole_0(B_1049,A_1050)
      | r1_xboole_0(A_1050,B_1049) ) ),
    inference(resolution,[status(thm)],[c_16,c_63488])).

tff(c_63594,plain,(
    ! [B_1051,A_1052] :
      ( r1_xboole_0(B_1051,A_1052)
      | k3_xboole_0(A_1052,B_1051) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_63521])).

tff(c_63617,plain,(
    ! [B_1051,A_1052] :
      ( k3_xboole_0(B_1051,A_1052) = k1_xboole_0
      | k3_xboole_0(A_1052,B_1051) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_63594,c_6])).

tff(c_71479,plain,(
    k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_71355,c_63617])).

tff(c_71312,plain,(
    ! [B_1215,C_1216] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_1215,C_1216),B_1215),k1_xboole_0) = k3_xboole_0(k4_xboole_0(k2_xboole_0(B_1215,C_1216),B_1215),C_1216) ),
    inference(superposition,[status(thm),theory(equality)],[c_63016,c_71073])).

tff(c_71402,plain,(
    ! [C_1216,B_1215] : k3_xboole_0(C_1216,k4_xboole_0(C_1216,B_1215)) = k4_xboole_0(C_1216,B_1215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62952,c_4,c_62952,c_22,c_71312])).

tff(c_63002,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,k4_xboole_0(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_62990])).

tff(c_75047,plain,(
    ! [A_1247,B_1248] : k4_xboole_0(A_1247,k3_xboole_0(A_1247,B_1248)) = k4_xboole_0(A_1247,B_1248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71402,c_63002])).

tff(c_75153,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_71479,c_75047])).

tff(c_75222,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72429,c_69711,c_26,c_26,c_75153])).

tff(c_63216,plain,(
    ! [C_1025] :
      ( ~ r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
      | ~ r2_hidden(C_1025,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62903,c_63202])).

tff(c_63232,plain,(
    ! [C_1025] : ~ r2_hidden(C_1025,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62891,c_63216])).

tff(c_62946,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),k4_xboole_0(B_18,A_17)) = k4_xboole_0(A_17,k4_xboole_0(B_18,A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_62930])).

tff(c_68276,plain,(
    ! [A_1189,B_1190] : k4_xboole_0(A_1189,k4_xboole_0(B_1190,A_1189)) = A_1189 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64190,c_62946])).

tff(c_68311,plain,(
    ! [A_1189,B_1190] : k3_xboole_0(A_1189,k4_xboole_0(B_1190,A_1189)) = k4_xboole_0(A_1189,A_1189) ),
    inference(superposition,[status(thm),theory(equality)],[c_68276,c_28])).

tff(c_68700,plain,(
    ! [A_1193,B_1194] : k3_xboole_0(A_1193,k4_xboole_0(B_1194,A_1193)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63016,c_68311])).

tff(c_63446,plain,(
    ! [A_1043,B_1044] :
      ( r2_hidden('#skF_2'(A_1043,B_1044),k3_xboole_0(A_1043,B_1044))
      | r1_xboole_0(A_1043,B_1044) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_63470,plain,(
    ! [B_4,A_3] :
      ( r2_hidden('#skF_2'(B_4,A_3),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(B_4,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_63446])).

tff(c_68728,plain,(
    ! [B_1194,A_1193] :
      ( r2_hidden('#skF_2'(k4_xboole_0(B_1194,A_1193),A_1193),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(B_1194,A_1193),A_1193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68700,c_63470])).

tff(c_68843,plain,(
    ! [B_1194,A_1193] : r1_xboole_0(k4_xboole_0(B_1194,A_1193),A_1193) ),
    inference(negUnitSimplification,[status(thm)],[c_63232,c_68728])).

tff(c_75280,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_75222,c_68843])).

tff(c_75330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62924,c_75280])).

tff(c_75331,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62923])).

tff(c_75336,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_75331])).

tff(c_75579,plain,(
    ! [A_1267,B_1268] : k4_xboole_0(k2_xboole_0(A_1267,B_1268),B_1268) = k4_xboole_0(A_1267,B_1268) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_75607,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75579])).

tff(c_75592,plain,(
    ! [A_1267] : k4_xboole_0(A_1267,k1_xboole_0) = k2_xboole_0(A_1267,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75579,c_22])).

tff(c_75618,plain,(
    ! [A_1267] : k2_xboole_0(A_1267,k1_xboole_0) = A_1267 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_75592])).

tff(c_75426,plain,(
    ! [A_1256,B_1257] : k4_xboole_0(A_1256,k4_xboole_0(A_1256,B_1257)) = k3_xboole_0(A_1256,B_1257) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_75444,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_75426])).

tff(c_75448,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_75444])).

tff(c_75798,plain,(
    ! [A_1276,B_1277,C_1278] : k4_xboole_0(k4_xboole_0(A_1276,B_1277),C_1278) = k4_xboole_0(A_1276,k2_xboole_0(B_1277,C_1278)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78913,plain,(
    ! [C_1387,A_1388,B_1389] : k2_xboole_0(C_1387,k4_xboole_0(A_1388,k2_xboole_0(B_1389,C_1387))) = k2_xboole_0(C_1387,k4_xboole_0(A_1388,B_1389)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75798,c_20])).

tff(c_79051,plain,(
    ! [C_1387,B_1389] : k2_xboole_0(C_1387,k4_xboole_0(k2_xboole_0(B_1389,C_1387),B_1389)) = k2_xboole_0(C_1387,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75448,c_78913])).

tff(c_79091,plain,(
    ! [C_1387,B_1389] : k2_xboole_0(C_1387,k4_xboole_0(C_1387,B_1389)) = C_1387 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75607,c_75618,c_79051])).

tff(c_75332,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62923])).

tff(c_75340,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75332,c_6])).

tff(c_77975,plain,(
    ! [A_1364,B_1365] : k4_xboole_0(A_1364,k3_xboole_0(A_1364,B_1365)) = k3_xboole_0(A_1364,k4_xboole_0(A_1364,B_1365)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75426,c_28])).

tff(c_78033,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75340,c_77975])).

tff(c_78058,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_78033])).

tff(c_79092,plain,(
    ! [C_1390,B_1391] : k2_xboole_0(C_1390,k4_xboole_0(C_1390,B_1391)) = C_1390 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75607,c_75618,c_79051])).

tff(c_79263,plain,(
    ! [A_1392,B_1393] : k2_xboole_0(A_1392,k3_xboole_0(A_1392,B_1393)) = A_1392 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_79092])).

tff(c_79852,plain,(
    ! [B_1400,A_1401] : k2_xboole_0(B_1400,k3_xboole_0(A_1401,B_1400)) = B_1400 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_79263])).

tff(c_75808,plain,(
    ! [A_1276,B_1277] : k4_xboole_0(A_1276,k2_xboole_0(B_1277,k4_xboole_0(A_1276,B_1277))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75798,c_75448])).

tff(c_75858,plain,(
    ! [A_1276,B_1277] : k4_xboole_0(A_1276,k2_xboole_0(B_1277,A_1276)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_75808])).

tff(c_80025,plain,(
    ! [A_1402,B_1403] : k4_xboole_0(k3_xboole_0(A_1402,B_1403),B_1403) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79852,c_75858])).

tff(c_80094,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78058,c_80025])).

tff(c_75914,plain,(
    ! [A_1283,B_1284] : k4_xboole_0(A_1283,k2_xboole_0(B_1284,A_1283)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_75808])).

tff(c_75929,plain,(
    ! [A_1283,B_1284] : k3_xboole_0(A_1283,k2_xboole_0(B_1284,A_1283)) = k4_xboole_0(A_1283,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75914,c_28])).

tff(c_75963,plain,(
    ! [A_1283,B_1284] : k3_xboole_0(A_1283,k2_xboole_0(B_1284,A_1283)) = A_1283 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_75929])).

tff(c_75585,plain,(
    ! [A_1267,B_1268] : k4_xboole_0(k2_xboole_0(A_1267,B_1268),k4_xboole_0(A_1267,B_1268)) = k3_xboole_0(k2_xboole_0(A_1267,B_1268),B_1268) ),
    inference(superposition,[status(thm),theory(equality)],[c_75579,c_28])).

tff(c_75616,plain,(
    ! [A_1267,B_1268] : k4_xboole_0(k2_xboole_0(A_1267,B_1268),k4_xboole_0(A_1267,B_1268)) = k3_xboole_0(B_1268,k2_xboole_0(A_1267,B_1268)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_75585])).

tff(c_79682,plain,(
    ! [A_1267,B_1268] : k4_xboole_0(k2_xboole_0(A_1267,B_1268),k4_xboole_0(A_1267,B_1268)) = B_1268 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75963,c_75616])).

tff(c_80383,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')),k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_80094,c_79682])).

tff(c_80426,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_79091,c_80383])).

tff(c_78036,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62903,c_77975])).

tff(c_78059,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_78036])).

tff(c_80091,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78059,c_80025])).

tff(c_80447,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))),k1_xboole_0) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80091,c_79682])).

tff(c_80490,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_79091,c_80447])).

tff(c_75848,plain,(
    ! [A_1276,B_1277,B_26] : k4_xboole_0(A_1276,k2_xboole_0(B_1277,k4_xboole_0(k4_xboole_0(A_1276,B_1277),B_26))) = k3_xboole_0(k4_xboole_0(A_1276,B_1277),B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_75798])).

tff(c_83041,plain,(
    ! [A_1430,B_1431,B_1432] : k4_xboole_0(A_1430,k2_xboole_0(B_1431,k4_xboole_0(A_1430,k2_xboole_0(B_1431,B_1432)))) = k3_xboole_0(k4_xboole_0(A_1430,B_1431),B_1432) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75848])).

tff(c_83182,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) = k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_80490,c_83041])).

tff(c_83313,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_80426,c_75858,c_4,c_83182])).

tff(c_83315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75336,c_83313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.80/8.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.10/8.46  
% 16.10/8.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.10/8.46  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 16.10/8.46  
% 16.10/8.46  %Foreground sorts:
% 16.10/8.46  
% 16.10/8.46  
% 16.10/8.46  %Background operators:
% 16.10/8.46  
% 16.10/8.46  
% 16.10/8.46  %Foreground operators:
% 16.10/8.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.10/8.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.10/8.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.10/8.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.10/8.46  tff('#skF_7', type, '#skF_7': $i).
% 16.10/8.46  tff('#skF_5', type, '#skF_5': $i).
% 16.10/8.46  tff('#skF_6', type, '#skF_6': $i).
% 16.10/8.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.10/8.46  tff('#skF_3', type, '#skF_3': $i).
% 16.10/8.46  tff('#skF_8', type, '#skF_8': $i).
% 16.10/8.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.10/8.46  tff('#skF_4', type, '#skF_4': $i).
% 16.10/8.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.10/8.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.10/8.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.10/8.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.10/8.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.10/8.46  
% 16.27/8.51  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 16.27/8.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 16.27/8.51  tff(f_94, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 16.27/8.51  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 16.27/8.51  tff(f_71, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 16.27/8.51  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 16.27/8.51  tff(f_77, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 16.27/8.51  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.27/8.51  tff(f_73, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 16.27/8.51  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.27/8.51  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 16.27/8.51  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 16.27/8.51  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.27/8.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.27/8.51  tff(c_40, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.27/8.51  tff(c_43, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 16.27/8.51  tff(c_642, plain, (~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_43])).
% 16.27/8.51  tff(c_22, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.27/8.51  tff(c_296, plain, (![A_48, B_49]: (k4_xboole_0(k2_xboole_0(A_48, B_49), B_49)=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.27/8.51  tff(c_306, plain, (![A_48]: (k4_xboole_0(A_48, k1_xboole_0)=k2_xboole_0(A_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_296, c_22])).
% 16.27/8.51  tff(c_322, plain, (![A_48]: (k2_xboole_0(A_48, k1_xboole_0)=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_306])).
% 16.27/8.51  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.27/8.51  tff(c_30, plain, (![A_27]: (r1_xboole_0(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.27/8.51  tff(c_122, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.27/8.51  tff(c_130, plain, (![A_27]: (k3_xboole_0(A_27, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_122])).
% 16.27/8.51  tff(c_226, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.27/8.51  tff(c_241, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_226])).
% 16.27/8.51  tff(c_244, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_241])).
% 16.27/8.51  tff(c_677, plain, (![A_74, B_75, C_76]: (k4_xboole_0(k4_xboole_0(A_74, B_75), C_76)=k4_xboole_0(A_74, k2_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.27/8.51  tff(c_720, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k2_xboole_0(B_75, k4_xboole_0(A_74, B_75)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_677])).
% 16.27/8.51  tff(c_745, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k2_xboole_0(B_75, A_74))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_720])).
% 16.27/8.51  tff(c_26, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.27/8.51  tff(c_32, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.27/8.51  tff(c_186, plain, (r1_xboole_0('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_32])).
% 16.27/8.51  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.27/8.51  tff(c_190, plain, (k3_xboole_0('#skF_6', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_186, c_6])).
% 16.27/8.51  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.27/8.51  tff(c_437, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.27/8.51  tff(c_466, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(k4_xboole_0(A_25, B_26), A_25))), inference(superposition, [status(thm), theory('equality')], [c_28, c_437])).
% 16.27/8.51  tff(c_4432, plain, (![A_187, B_188]: (k2_xboole_0(k4_xboole_0(A_187, B_188), k3_xboole_0(A_187, B_188))=k2_xboole_0(A_187, k4_xboole_0(A_187, B_188)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_466])).
% 16.27/8.51  tff(c_4614, plain, (k2_xboole_0(k4_xboole_0('#skF_6', '#skF_8'), k1_xboole_0)=k2_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_4432])).
% 16.27/8.51  tff(c_4674, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_8'))=k4_xboole_0('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_4614])).
% 16.27/8.51  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.27/8.51  tff(c_460, plain, (![B_21, A_20]: (k2_xboole_0(B_21, k4_xboole_0(A_20, B_21))=k2_xboole_0(B_21, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_437])).
% 16.27/8.51  tff(c_1369, plain, (![B_99, A_100]: (k2_xboole_0(B_99, k2_xboole_0(A_100, B_99))=k2_xboole_0(B_99, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_460])).
% 16.27/8.51  tff(c_1428, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1369])).
% 16.27/8.51  tff(c_315, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_296])).
% 16.27/8.51  tff(c_749, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k2_xboole_0(B_78, A_77))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_720])).
% 16.27/8.51  tff(c_767, plain, (![A_77, B_78]: (k3_xboole_0(A_77, k2_xboole_0(B_78, A_77))=k4_xboole_0(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_749, c_28])).
% 16.27/8.51  tff(c_799, plain, (![A_77, B_78]: (k3_xboole_0(A_77, k2_xboole_0(B_78, A_77))=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_767])).
% 16.27/8.51  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.27/8.51  tff(c_302, plain, (![A_48, B_49]: (k4_xboole_0(k2_xboole_0(A_48, B_49), k4_xboole_0(A_48, B_49))=k3_xboole_0(k2_xboole_0(A_48, B_49), B_49))), inference(superposition, [status(thm), theory('equality')], [c_296, c_28])).
% 16.27/8.51  tff(c_321, plain, (![A_48, B_49]: (k4_xboole_0(k2_xboole_0(A_48, B_49), k4_xboole_0(A_48, B_49))=k3_xboole_0(B_49, k2_xboole_0(A_48, B_49)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_302])).
% 16.27/8.51  tff(c_3088, plain, (![A_156, B_157]: (k4_xboole_0(k2_xboole_0(A_156, B_157), k4_xboole_0(A_156, B_157))=B_157)), inference(demodulation, [status(thm), theory('equality')], [c_799, c_321])).
% 16.27/8.51  tff(c_3139, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(k2_xboole_0(A_1, B_2), A_1), k4_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_315, c_3088])).
% 16.27/8.51  tff(c_3192, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_2, c_3139])).
% 16.27/8.51  tff(c_5603, plain, (k4_xboole_0(k4_xboole_0('#skF_6', '#skF_8'), k4_xboole_0(k4_xboole_0('#skF_6', '#skF_8'), '#skF_6'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4674, c_3192])).
% 16.27/8.51  tff(c_5666, plain, (k4_xboole_0('#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_745, c_26, c_26, c_5603])).
% 16.27/8.51  tff(c_791, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_749])).
% 16.27/8.51  tff(c_36, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.27/8.51  tff(c_217, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_36])).
% 16.27/8.51  tff(c_221, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_217, c_6])).
% 16.27/8.51  tff(c_4608, plain, (k2_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), k1_xboole_0)=k2_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_221, c_4432])).
% 16.27/8.51  tff(c_4672, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))=k4_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_4608])).
% 16.27/8.51  tff(c_5008, plain, (k4_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), k4_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_6'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4672, c_3192])).
% 16.27/8.51  tff(c_5071, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_791, c_26, c_2, c_26, c_5008])).
% 16.27/8.51  tff(c_25771, plain, (![C_363]: (k4_xboole_0('#skF_6', k2_xboole_0('#skF_7', C_363))=k4_xboole_0('#skF_6', C_363))), inference(superposition, [status(thm), theory('equality')], [c_5071, c_26])).
% 16.27/8.51  tff(c_512, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_538, plain, (![A_27, C_58]: (~r1_xboole_0(A_27, k1_xboole_0) | ~r2_hidden(C_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_512])).
% 16.27/8.51  tff(c_552, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_538])).
% 16.27/8.51  tff(c_447, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), k4_xboole_0(B_54, A_53))=k4_xboole_0(A_53, k4_xboole_0(B_54, A_53)))), inference(superposition, [status(thm), theory('equality')], [c_437, c_24])).
% 16.27/8.51  tff(c_3533, plain, (![A_166, B_167]: (k4_xboole_0(A_166, k4_xboole_0(B_167, A_166))=A_166)), inference(demodulation, [status(thm), theory('equality')], [c_3192, c_447])).
% 16.27/8.51  tff(c_3565, plain, (![A_166, B_167]: (k3_xboole_0(A_166, k4_xboole_0(B_167, A_166))=k4_xboole_0(A_166, A_166))), inference(superposition, [status(thm), theory('equality')], [c_3533, c_28])).
% 16.27/8.51  tff(c_3658, plain, (![A_168, B_169]: (k3_xboole_0(A_168, k4_xboole_0(B_169, A_168))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_3565])).
% 16.27/8.51  tff(c_918, plain, (![A_83, B_84]: (r2_hidden('#skF_2'(A_83, B_84), k3_xboole_0(A_83, B_84)) | r1_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_951, plain, (![B_4, A_3]: (r2_hidden('#skF_2'(B_4, A_3), k3_xboole_0(A_3, B_4)) | r1_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_918])).
% 16.27/8.51  tff(c_3669, plain, (![B_169, A_168]: (r2_hidden('#skF_2'(k4_xboole_0(B_169, A_168), A_168), k1_xboole_0) | r1_xboole_0(k4_xboole_0(B_169, A_168), A_168))), inference(superposition, [status(thm), theory('equality')], [c_3658, c_951])).
% 16.27/8.51  tff(c_3757, plain, (![B_169, A_168]: (r1_xboole_0(k4_xboole_0(B_169, A_168), A_168))), inference(negUnitSimplification, [status(thm)], [c_552, c_3669])).
% 16.27/8.51  tff(c_27736, plain, (![C_374]: (r1_xboole_0(k4_xboole_0('#skF_6', C_374), k2_xboole_0('#skF_7', C_374)))), inference(superposition, [status(thm), theory('equality')], [c_25771, c_3757])).
% 16.27/8.51  tff(c_27834, plain, (r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5666, c_27736])).
% 16.27/8.51  tff(c_27907, plain, (r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_27834])).
% 16.27/8.51  tff(c_27909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_642, c_27907])).
% 16.27/8.51  tff(c_27911, plain, (r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_43])).
% 16.27/8.51  tff(c_42, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.27/8.51  tff(c_44, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 16.27/8.51  tff(c_28096, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27911, c_44])).
% 16.27/8.51  tff(c_28097, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_28096])).
% 16.27/8.51  tff(c_312, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_296])).
% 16.27/8.51  tff(c_27957, plain, (![A_377, B_378, C_379]: (k4_xboole_0(k4_xboole_0(A_377, B_378), C_379)=k4_xboole_0(A_377, k2_xboole_0(B_378, C_379)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.27/8.51  tff(c_31549, plain, (![C_463, A_464, B_465]: (k2_xboole_0(C_463, k4_xboole_0(A_464, k2_xboole_0(B_465, C_463)))=k2_xboole_0(C_463, k4_xboole_0(A_464, B_465)))), inference(superposition, [status(thm), theory('equality')], [c_27957, c_20])).
% 16.27/8.51  tff(c_31719, plain, (![C_463, B_465]: (k2_xboole_0(C_463, k4_xboole_0(k2_xboole_0(B_465, C_463), B_465))=k2_xboole_0(C_463, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_31549])).
% 16.27/8.51  tff(c_31771, plain, (![C_466, B_467]: (k2_xboole_0(C_466, k4_xboole_0(C_466, B_467))=C_466)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_322, c_31719])).
% 16.27/8.51  tff(c_28000, plain, (![A_377, B_378]: (k4_xboole_0(A_377, k2_xboole_0(B_378, k4_xboole_0(A_377, B_378)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_27957])).
% 16.27/8.51  tff(c_28038, plain, (![A_380, B_381]: (k4_xboole_0(A_380, k2_xboole_0(B_381, A_380))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28000])).
% 16.27/8.51  tff(c_28056, plain, (![A_380, B_381]: (k3_xboole_0(A_380, k2_xboole_0(B_381, A_380))=k4_xboole_0(A_380, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28038, c_28])).
% 16.27/8.51  tff(c_28088, plain, (![A_380, B_381]: (k3_xboole_0(A_380, k2_xboole_0(B_381, A_380))=A_380)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28056])).
% 16.27/8.51  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.27/8.51  tff(c_245, plain, (![A_44]: (k4_xboole_0(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_241])).
% 16.27/8.51  tff(c_250, plain, (![A_44]: (k4_xboole_0(A_44, k1_xboole_0)=k3_xboole_0(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_245, c_28])).
% 16.27/8.51  tff(c_262, plain, (![A_44]: (k3_xboole_0(A_44, A_44)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_250])).
% 16.27/8.51  tff(c_574, plain, (![A_61, C_62]: (~r1_xboole_0(A_61, A_61) | ~r2_hidden(C_62, A_61))), inference(superposition, [status(thm), theory('equality')], [c_262, c_512])).
% 16.27/8.51  tff(c_580, plain, (![C_62, B_6]: (~r2_hidden(C_62, B_6) | k3_xboole_0(B_6, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_574])).
% 16.27/8.51  tff(c_605, plain, (![C_66, B_67]: (~r2_hidden(C_66, B_67) | k1_xboole_0!=B_67)), inference(demodulation, [status(thm), theory('equality')], [c_262, c_580])).
% 16.27/8.51  tff(c_630, plain, (![B_70, A_71]: (k1_xboole_0!=B_70 | r1_xboole_0(A_71, B_70))), inference(resolution, [status(thm)], [c_12, c_605])).
% 16.27/8.51  tff(c_28545, plain, (![A_398, B_399]: (k3_xboole_0(A_398, B_399)=k1_xboole_0 | k1_xboole_0!=B_399)), inference(resolution, [status(thm)], [c_630, c_6])).
% 16.27/8.51  tff(c_28608, plain, (![A_380, B_381]: (k1_xboole_0=A_380 | k2_xboole_0(B_381, A_380)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28088, c_28545])).
% 16.27/8.51  tff(c_34888, plain, (![C_503, B_504]: (k4_xboole_0(C_503, B_504)=k1_xboole_0 | k1_xboole_0!=C_503)), inference(superposition, [status(thm), theory('equality')], [c_31771, c_28608])).
% 16.27/8.51  tff(c_35026, plain, (![B_504, C_503]: (k2_xboole_0(B_504, k1_xboole_0)=k2_xboole_0(B_504, C_503) | k1_xboole_0!=C_503)), inference(superposition, [status(thm), theory('equality')], [c_34888, c_20])).
% 16.27/8.51  tff(c_35699, plain, (![B_504]: (k2_xboole_0(B_504, k1_xboole_0)=B_504)), inference(demodulation, [status(thm), theory('equality')], [c_322, c_35026])).
% 16.27/8.51  tff(c_32883, plain, (![A_48, B_49]: (k4_xboole_0(k2_xboole_0(A_48, B_49), k4_xboole_0(A_48, B_49))=B_49)), inference(demodulation, [status(thm), theory('equality')], [c_28088, c_321])).
% 16.27/8.51  tff(c_34938, plain, (![C_503, B_504]: (k4_xboole_0(k2_xboole_0(C_503, B_504), k1_xboole_0)=B_504 | k1_xboole_0!=C_503)), inference(superposition, [status(thm), theory('equality')], [c_34888, c_32883])).
% 16.27/8.51  tff(c_35988, plain, (![B_504]: (k2_xboole_0(k1_xboole_0, B_504)=B_504)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_34938])).
% 16.27/8.51  tff(c_31766, plain, (![C_463, B_465]: (k2_xboole_0(C_463, k4_xboole_0(C_463, B_465))=C_463)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_322, c_31719])).
% 16.27/8.51  tff(c_27910, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_43])).
% 16.27/8.51  tff(c_27918, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_27910, c_6])).
% 16.27/8.51  tff(c_477, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(A_25, k4_xboole_0(A_25, B_26)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_466])).
% 16.27/8.51  tff(c_36742, plain, (![A_520, B_521]: (k2_xboole_0(k4_xboole_0(A_520, B_521), k3_xboole_0(A_520, B_521))=A_520)), inference(demodulation, [status(thm), theory('equality')], [c_31766, c_477])).
% 16.27/8.51  tff(c_36964, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_27918, c_36742])).
% 16.27/8.51  tff(c_29192, plain, (![B_420, A_421]: (k2_xboole_0(B_420, k2_xboole_0(A_421, B_420))=k2_xboole_0(B_420, A_421))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_460])).
% 16.27/8.51  tff(c_29251, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_29192])).
% 16.27/8.51  tff(c_37383, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36964, c_29251])).
% 16.27/8.51  tff(c_37465, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_35988, c_31766, c_2, c_2, c_37383])).
% 16.27/8.51  tff(c_28025, plain, (![A_377, B_378]: (k4_xboole_0(A_377, k2_xboole_0(B_378, A_377))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28000])).
% 16.27/8.51  tff(c_31848, plain, (![C_466, B_467]: (k4_xboole_0(k4_xboole_0(C_466, B_467), C_466)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_31771, c_28025])).
% 16.27/8.51  tff(c_27973, plain, (![A_377, B_378, C_379]: (k4_xboole_0(k4_xboole_0(A_377, B_378), k4_xboole_0(A_377, k2_xboole_0(B_378, C_379)))=k3_xboole_0(k4_xboole_0(A_377, B_378), C_379))), inference(superposition, [status(thm), theory('equality')], [c_27957, c_28])).
% 16.27/8.51  tff(c_37504, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_37465, c_27973])).
% 16.27/8.51  tff(c_37573, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_31848, c_4, c_37504])).
% 16.27/8.51  tff(c_28178, plain, (![A_384, B_385]: (r2_hidden('#skF_2'(A_384, B_385), k3_xboole_0(A_384, B_385)) | r1_xboole_0(A_384, B_385))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_28214, plain, (![B_4, A_3]: (r2_hidden('#skF_2'(B_4, A_3), k3_xboole_0(A_3, B_4)) | r1_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_28178])).
% 16.27/8.51  tff(c_37616, plain, (r2_hidden('#skF_2'(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0) | r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_37573, c_28214])).
% 16.27/8.51  tff(c_37675, plain, (r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_552, c_37616])).
% 16.27/8.51  tff(c_37707, plain, (k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_37675, c_6])).
% 16.27/8.51  tff(c_35187, plain, (![A_505, B_506, C_507]: (k4_xboole_0(k4_xboole_0(A_505, B_506), k4_xboole_0(A_505, k2_xboole_0(B_506, C_507)))=k3_xboole_0(k4_xboole_0(A_505, B_506), C_507))), inference(superposition, [status(thm), theory('equality')], [c_27957, c_28])).
% 16.27/8.51  tff(c_35427, plain, (![B_506, C_507]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_506, C_507), B_506), k1_xboole_0)=k3_xboole_0(k4_xboole_0(k2_xboole_0(B_506, C_507), B_506), C_507))), inference(superposition, [status(thm), theory('equality')], [c_244, c_35187])).
% 16.27/8.51  tff(c_35504, plain, (![C_507, B_506]: (k3_xboole_0(C_507, k4_xboole_0(C_507, B_506))=k4_xboole_0(C_507, B_506))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_4, c_312, c_22, c_35427])).
% 16.27/8.51  tff(c_229, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k3_xboole_0(A_42, k4_xboole_0(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_28])).
% 16.27/8.51  tff(c_37709, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_35504, c_229])).
% 16.27/8.51  tff(c_38347, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_37707, c_37709])).
% 16.27/8.51  tff(c_38434, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_35699, c_37465, c_26, c_26, c_38347])).
% 16.27/8.51  tff(c_33228, plain, (![A_484, B_485]: (k4_xboole_0(k2_xboole_0(A_484, B_485), k4_xboole_0(B_485, A_484))=k4_xboole_0(A_484, k4_xboole_0(B_485, A_484)))), inference(superposition, [status(thm), theory('equality')], [c_437, c_24])).
% 16.27/8.51  tff(c_33377, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), k4_xboole_0(B_2, A_1))=k4_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_33228])).
% 16.27/8.51  tff(c_33475, plain, (![A_486, B_487]: (k4_xboole_0(A_486, k4_xboole_0(B_487, A_486))=A_486)), inference(demodulation, [status(thm), theory('equality')], [c_32883, c_33377])).
% 16.27/8.51  tff(c_33513, plain, (![A_486, B_487]: (k3_xboole_0(A_486, k4_xboole_0(B_487, A_486))=k4_xboole_0(A_486, A_486))), inference(superposition, [status(thm), theory('equality')], [c_33475, c_28])).
% 16.27/8.51  tff(c_33646, plain, (![A_488, B_489]: (k3_xboole_0(A_488, k4_xboole_0(B_489, A_488))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_33513])).
% 16.27/8.51  tff(c_33663, plain, (![B_489, A_488]: (r2_hidden('#skF_2'(k4_xboole_0(B_489, A_488), A_488), k1_xboole_0) | r1_xboole_0(k4_xboole_0(B_489, A_488), A_488))), inference(superposition, [status(thm), theory('equality')], [c_33646, c_28214])).
% 16.27/8.51  tff(c_33786, plain, (![B_489, A_488]: (r1_xboole_0(k4_xboole_0(B_489, A_488), A_488))), inference(negUnitSimplification, [status(thm)], [c_552, c_33663])).
% 16.27/8.51  tff(c_38499, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38434, c_33786])).
% 16.27/8.51  tff(c_38546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28097, c_38499])).
% 16.27/8.51  tff(c_38547, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_28096])).
% 16.27/8.51  tff(c_38560, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_38547])).
% 16.27/8.51  tff(c_41778, plain, (![C_622, A_623, B_624]: (k2_xboole_0(C_622, k4_xboole_0(A_623, k2_xboole_0(B_624, C_622)))=k2_xboole_0(C_622, k4_xboole_0(A_623, B_624)))), inference(superposition, [status(thm), theory('equality')], [c_27957, c_20])).
% 16.27/8.51  tff(c_41923, plain, (![C_622, B_624]: (k2_xboole_0(C_622, k4_xboole_0(k2_xboole_0(B_624, C_622), B_624))=k2_xboole_0(C_622, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_41778])).
% 16.27/8.51  tff(c_41960, plain, (![C_622, B_624]: (k2_xboole_0(C_622, k4_xboole_0(C_622, B_624))=C_622)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_322, c_41923])).
% 16.27/8.51  tff(c_38548, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_28096])).
% 16.27/8.51  tff(c_38567, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38548, c_6])).
% 16.27/8.51  tff(c_40939, plain, (![A_602, B_603]: (k4_xboole_0(A_602, k3_xboole_0(A_602, B_603))=k3_xboole_0(A_602, k4_xboole_0(A_602, B_603)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_28])).
% 16.27/8.51  tff(c_40995, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38567, c_40939])).
% 16.27/8.51  tff(c_41042, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_40995])).
% 16.27/8.51  tff(c_41963, plain, (![C_625, B_626]: (k2_xboole_0(C_625, k4_xboole_0(C_625, B_626))=C_625)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_322, c_41923])).
% 16.27/8.51  tff(c_42196, plain, (![A_627, B_628]: (k2_xboole_0(A_627, k3_xboole_0(A_627, B_628))=A_627)), inference(superposition, [status(thm), theory('equality')], [c_28, c_41963])).
% 16.27/8.51  tff(c_42826, plain, (![A_636, B_637]: (k2_xboole_0(A_636, k3_xboole_0(B_637, A_636))=A_636)), inference(superposition, [status(thm), theory('equality')], [c_4, c_42196])).
% 16.27/8.51  tff(c_42875, plain, (![B_637, A_636]: (k4_xboole_0(k3_xboole_0(B_637, A_636), A_636)=k4_xboole_0(A_636, A_636))), inference(superposition, [status(thm), theory('equality')], [c_42826, c_312])).
% 16.27/8.51  tff(c_43314, plain, (![B_642, A_643]: (k4_xboole_0(k3_xboole_0(B_642, A_643), A_643)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_42875])).
% 16.27/8.51  tff(c_43365, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41042, c_43314])).
% 16.27/8.51  tff(c_42499, plain, (![A_48, B_49]: (k4_xboole_0(k2_xboole_0(A_48, B_49), k4_xboole_0(A_48, B_49))=B_49)), inference(demodulation, [status(thm), theory('equality')], [c_28088, c_321])).
% 16.27/8.51  tff(c_44999, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4')), k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_43365, c_42499])).
% 16.27/8.51  tff(c_45035, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_41960, c_44999])).
% 16.27/8.51  tff(c_42030, plain, (![C_625, B_626]: (k4_xboole_0(k4_xboole_0(C_625, B_626), C_625)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_41963, c_28025])).
% 16.27/8.51  tff(c_39130, plain, (![A_544, B_545]: (k3_xboole_0(A_544, B_545)=k1_xboole_0 | k1_xboole_0!=B_545)), inference(resolution, [status(thm)], [c_630, c_6])).
% 16.27/8.51  tff(c_39153, plain, (![A_544, B_381]: (k1_xboole_0=A_544 | k2_xboole_0(B_381, A_544)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_39130, c_28088])).
% 16.27/8.51  tff(c_45512, plain, (![C_666, B_667]: (k4_xboole_0(C_666, B_667)=k1_xboole_0 | k1_xboole_0!=C_666)), inference(superposition, [status(thm), theory('equality')], [c_41963, c_39153])).
% 16.27/8.51  tff(c_45591, plain, (![C_666, B_667]: (k4_xboole_0(k2_xboole_0(C_666, B_667), k1_xboole_0)=B_667 | k1_xboole_0!=C_666)), inference(superposition, [status(thm), theory('equality')], [c_45512, c_42499])).
% 16.27/8.51  tff(c_46732, plain, (![B_667]: (k2_xboole_0(k1_xboole_0, B_667)=B_667)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_45591])).
% 16.27/8.51  tff(c_47945, plain, (![A_685, B_686]: (k2_xboole_0(k4_xboole_0(A_685, B_686), k3_xboole_0(A_685, B_686))=A_685)), inference(demodulation, [status(thm), theory('equality')], [c_41960, c_477])).
% 16.27/8.51  tff(c_48193, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_27918, c_47945])).
% 16.27/8.51  tff(c_39531, plain, (![B_555, A_556]: (k4_xboole_0(k2_xboole_0(B_555, A_556), B_555)=k4_xboole_0(A_556, B_555))), inference(superposition, [status(thm), theory('equality')], [c_2, c_296])).
% 16.27/8.51  tff(c_39540, plain, (![B_555, A_556]: (k2_xboole_0(B_555, k4_xboole_0(A_556, B_555))=k2_xboole_0(B_555, k2_xboole_0(B_555, A_556)))), inference(superposition, [status(thm), theory('equality')], [c_39531, c_20])).
% 16.27/8.51  tff(c_39586, plain, (![B_555, A_556]: (k2_xboole_0(B_555, k2_xboole_0(B_555, A_556))=k2_xboole_0(B_555, A_556))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_39540])).
% 16.27/8.51  tff(c_48478, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48193, c_39586])).
% 16.27/8.51  tff(c_48562, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46732, c_41960, c_2, c_2, c_48478])).
% 16.27/8.51  tff(c_48602, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48562, c_27973])).
% 16.27/8.51  tff(c_48674, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_45035, c_42030, c_4, c_48602])).
% 16.27/8.51  tff(c_48676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38560, c_48674])).
% 16.27/8.51  tff(c_48678, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_36])).
% 16.27/8.51  tff(c_38, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.27/8.51  tff(c_48875, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48678, c_38])).
% 16.27/8.51  tff(c_48876, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48875])).
% 16.27/8.51  tff(c_48677, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_36])).
% 16.27/8.51  tff(c_48686, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_48677, c_6])).
% 16.27/8.51  tff(c_48691, plain, (![A_690, B_691]: (k4_xboole_0(k2_xboole_0(A_690, B_691), B_691)=k4_xboole_0(A_690, B_691))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.27/8.51  tff(c_48707, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_48691])).
% 16.27/8.51  tff(c_48698, plain, (![A_690]: (k4_xboole_0(A_690, k1_xboole_0)=k2_xboole_0(A_690, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48691, c_22])).
% 16.27/8.51  tff(c_48713, plain, (![A_690]: (k2_xboole_0(A_690, k1_xboole_0)=A_690)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_48698])).
% 16.27/8.51  tff(c_48805, plain, (![A_695, B_696]: (k4_xboole_0(A_695, k4_xboole_0(A_695, B_696))=k3_xboole_0(A_695, B_696))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.27/8.51  tff(c_48829, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_48805])).
% 16.27/8.51  tff(c_48834, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_48829])).
% 16.27/8.51  tff(c_49464, plain, (![A_734, B_735, C_736]: (k4_xboole_0(k4_xboole_0(A_734, B_735), C_736)=k4_xboole_0(A_734, k2_xboole_0(B_735, C_736)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.27/8.51  tff(c_51982, plain, (![C_815, A_816, B_817]: (k2_xboole_0(C_815, k4_xboole_0(A_816, k2_xboole_0(B_817, C_815)))=k2_xboole_0(C_815, k4_xboole_0(A_816, B_817)))), inference(superposition, [status(thm), theory('equality')], [c_49464, c_20])).
% 16.27/8.51  tff(c_52078, plain, (![C_815, B_817]: (k2_xboole_0(C_815, k4_xboole_0(k2_xboole_0(B_817, C_815), B_817))=k2_xboole_0(C_815, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48834, c_51982])).
% 16.27/8.51  tff(c_52117, plain, (![C_815, B_817]: (k2_xboole_0(C_815, k4_xboole_0(C_815, B_817))=C_815)), inference(demodulation, [status(thm), theory('equality')], [c_48707, c_48713, c_52078])).
% 16.27/8.51  tff(c_48975, plain, (![A_704, B_705]: (k2_xboole_0(A_704, k4_xboole_0(B_705, A_704))=k2_xboole_0(A_704, B_705))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.27/8.51  tff(c_48997, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(k4_xboole_0(A_25, B_26), A_25))), inference(superposition, [status(thm), theory('equality')], [c_28, c_48975])).
% 16.27/8.51  tff(c_49013, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(A_25, k4_xboole_0(A_25, B_26)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48997])).
% 16.27/8.51  tff(c_55289, plain, (![A_852, B_853]: (k2_xboole_0(k4_xboole_0(A_852, B_853), k3_xboole_0(A_852, B_853))=A_852)), inference(demodulation, [status(thm), theory('equality')], [c_52117, c_49013])).
% 16.27/8.51  tff(c_55466, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_48686, c_55289])).
% 16.27/8.51  tff(c_52122, plain, (![C_818, B_819]: (k2_xboole_0(C_818, k4_xboole_0(C_818, B_819))=C_818)), inference(demodulation, [status(thm), theory('equality')], [c_48707, c_48713, c_52078])).
% 16.27/8.51  tff(c_49477, plain, (![A_734, B_735]: (k4_xboole_0(A_734, k2_xboole_0(B_735, k4_xboole_0(A_734, B_735)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49464, c_48834])).
% 16.27/8.51  tff(c_49540, plain, (![A_737, B_738]: (k4_xboole_0(A_737, k2_xboole_0(B_738, A_737))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_49477])).
% 16.27/8.51  tff(c_49558, plain, (![A_737, B_738]: (k3_xboole_0(A_737, k2_xboole_0(B_738, A_737))=k4_xboole_0(A_737, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_49540, c_28])).
% 16.27/8.51  tff(c_49687, plain, (![A_742, B_743]: (k3_xboole_0(A_742, k2_xboole_0(B_743, A_742))=A_742)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_49558])).
% 16.27/8.51  tff(c_48883, plain, (![A_701]: (k4_xboole_0(A_701, A_701)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_48829])).
% 16.27/8.51  tff(c_48888, plain, (![A_701]: (k4_xboole_0(A_701, k1_xboole_0)=k3_xboole_0(A_701, A_701))), inference(superposition, [status(thm), theory('equality')], [c_48883, c_28])).
% 16.27/8.51  tff(c_48900, plain, (![A_701]: (k3_xboole_0(A_701, A_701)=A_701)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_48888])).
% 16.27/8.51  tff(c_48904, plain, (![A_702]: (k3_xboole_0(A_702, A_702)=A_702)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_48888])).
% 16.27/8.51  tff(c_18, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_49050, plain, (![A_707, C_708]: (~r1_xboole_0(A_707, A_707) | ~r2_hidden(C_708, A_707))), inference(superposition, [status(thm), theory('equality')], [c_48904, c_18])).
% 16.27/8.51  tff(c_49053, plain, (![C_708, B_6]: (~r2_hidden(C_708, B_6) | k3_xboole_0(B_6, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_49050])).
% 16.27/8.51  tff(c_49062, plain, (![C_709, B_710]: (~r2_hidden(C_709, B_710) | k1_xboole_0!=B_710)), inference(demodulation, [status(thm), theory('equality')], [c_48900, c_49053])).
% 16.27/8.51  tff(c_49069, plain, (![B_711, A_712]: (k1_xboole_0!=B_711 | r1_xboole_0(A_712, B_711))), inference(resolution, [status(thm)], [c_12, c_49062])).
% 16.27/8.51  tff(c_49085, plain, (![A_712, B_711]: (k3_xboole_0(A_712, B_711)=k1_xboole_0 | k1_xboole_0!=B_711)), inference(resolution, [status(thm)], [c_49069, c_6])).
% 16.27/8.51  tff(c_49699, plain, (![A_742, B_743]: (k1_xboole_0=A_742 | k2_xboole_0(B_743, A_742)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49687, c_49085])).
% 16.27/8.51  tff(c_53814, plain, (![C_837, B_838]: (k4_xboole_0(C_837, B_838)=k1_xboole_0 | k1_xboole_0!=C_837)), inference(superposition, [status(thm), theory('equality')], [c_52122, c_49699])).
% 16.27/8.51  tff(c_53932, plain, (![B_838, C_837]: (k2_xboole_0(B_838, k1_xboole_0)=k2_xboole_0(B_838, C_837) | k1_xboole_0!=C_837)), inference(superposition, [status(thm), theory('equality')], [c_53814, c_20])).
% 16.27/8.51  tff(c_54036, plain, (![B_838, C_837]: (k2_xboole_0(B_838, C_837)=B_838 | k1_xboole_0!=C_837)), inference(demodulation, [status(thm), theory('equality')], [c_48713, c_53932])).
% 16.27/8.51  tff(c_55864, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_55466, c_54036])).
% 16.27/8.51  tff(c_48835, plain, (![A_697, B_698, C_699]: (~r1_xboole_0(A_697, B_698) | ~r2_hidden(C_699, k3_xboole_0(A_697, B_698)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_48854, plain, (![A_27, C_699]: (~r1_xboole_0(A_27, k1_xboole_0) | ~r2_hidden(C_699, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_48835])).
% 16.27/8.51  tff(c_48867, plain, (![C_699]: (~r2_hidden(C_699, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_48854])).
% 16.27/8.51  tff(c_49346, plain, (![A_730, B_731]: (k4_xboole_0(k2_xboole_0(A_730, B_731), A_730)=k4_xboole_0(B_731, A_730))), inference(superposition, [status(thm), theory('equality')], [c_2, c_48691])).
% 16.27/8.51  tff(c_49372, plain, (![B_18, A_17]: (k4_xboole_0(k4_xboole_0(B_18, A_17), A_17)=k4_xboole_0(k2_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_49346])).
% 16.27/8.51  tff(c_50437, plain, (![B_779, A_780]: (k4_xboole_0(k4_xboole_0(B_779, A_780), A_780)=k4_xboole_0(B_779, A_780))), inference(demodulation, [status(thm), theory('equality')], [c_48707, c_49372])).
% 16.27/8.51  tff(c_50455, plain, (![B_779, A_780]: (k4_xboole_0(k4_xboole_0(B_779, A_780), k4_xboole_0(B_779, A_780))=k3_xboole_0(k4_xboole_0(B_779, A_780), A_780))), inference(superposition, [status(thm), theory('equality')], [c_50437, c_28])).
% 16.27/8.51  tff(c_50506, plain, (![A_780, B_779]: (k3_xboole_0(A_780, k4_xboole_0(B_779, A_780))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48834, c_4, c_50455])).
% 16.27/8.51  tff(c_49807, plain, (![A_746, B_747]: (r2_hidden('#skF_2'(A_746, B_747), k3_xboole_0(A_746, B_747)) | r1_xboole_0(A_746, B_747))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_50659, plain, (![B_785, A_786]: (r2_hidden('#skF_2'(B_785, A_786), k3_xboole_0(A_786, B_785)) | r1_xboole_0(B_785, A_786))), inference(superposition, [status(thm), theory('equality')], [c_4, c_49807])).
% 16.27/8.51  tff(c_50673, plain, (![B_779, A_780]: (r2_hidden('#skF_2'(k4_xboole_0(B_779, A_780), A_780), k1_xboole_0) | r1_xboole_0(k4_xboole_0(B_779, A_780), A_780))), inference(superposition, [status(thm), theory('equality')], [c_50506, c_50659])).
% 16.27/8.51  tff(c_50722, plain, (![B_787, A_788]: (r1_xboole_0(k4_xboole_0(B_787, A_788), A_788))), inference(negUnitSimplification, [status(thm)], [c_48867, c_50673])).
% 16.27/8.51  tff(c_51073, plain, (![A_797, B_798, C_799]: (r1_xboole_0(k4_xboole_0(A_797, k2_xboole_0(B_798, C_799)), C_799))), inference(superposition, [status(thm), theory('equality')], [c_26, c_50722])).
% 16.27/8.51  tff(c_51132, plain, (![A_797, A_1, B_2]: (r1_xboole_0(k4_xboole_0(A_797, k2_xboole_0(A_1, B_2)), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_51073])).
% 16.27/8.51  tff(c_56178, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_55864, c_51132])).
% 16.27/8.51  tff(c_56247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48876, c_56178])).
% 16.27/8.51  tff(c_56248, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_48875])).
% 16.27/8.51  tff(c_56936, plain, (![A_892, B_893, C_894]: (k4_xboole_0(k4_xboole_0(A_892, B_893), C_894)=k4_xboole_0(A_892, k2_xboole_0(B_893, C_894)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.27/8.51  tff(c_62303, plain, (![C_1002, A_1003, B_1004]: (k2_xboole_0(C_1002, k4_xboole_0(A_1003, k2_xboole_0(B_1004, C_1002)))=k2_xboole_0(C_1002, k4_xboole_0(A_1003, B_1004)))), inference(superposition, [status(thm), theory('equality')], [c_56936, c_20])).
% 16.27/8.51  tff(c_62462, plain, (![C_1002, B_1004]: (k2_xboole_0(C_1002, k4_xboole_0(k2_xboole_0(B_1004, C_1002), B_1004))=k2_xboole_0(C_1002, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48834, c_62303])).
% 16.27/8.51  tff(c_62518, plain, (![C_1002, B_1004]: (k2_xboole_0(C_1002, k4_xboole_0(C_1002, B_1004))=C_1002)), inference(demodulation, [status(thm), theory('equality')], [c_48707, c_48713, c_62462])).
% 16.27/8.51  tff(c_56280, plain, (![A_859, B_860]: (k2_xboole_0(A_859, k4_xboole_0(B_860, A_859))=k2_xboole_0(A_859, B_860))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.27/8.51  tff(c_56299, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(k4_xboole_0(A_25, B_26), A_25))), inference(superposition, [status(thm), theory('equality')], [c_28, c_56280])).
% 16.27/8.51  tff(c_60233, plain, (![A_975, B_976]: (k2_xboole_0(k4_xboole_0(A_975, B_976), k3_xboole_0(A_975, B_976))=k2_xboole_0(A_975, k4_xboole_0(A_975, B_976)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56299])).
% 16.27/8.51  tff(c_60392, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_xboole_0)=k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_48686, c_60233])).
% 16.27/8.51  tff(c_60455, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48713, c_60392])).
% 16.27/8.51  tff(c_62523, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62518, c_60455])).
% 16.27/8.51  tff(c_56949, plain, (![A_892, B_893]: (k4_xboole_0(A_892, k2_xboole_0(B_893, k4_xboole_0(A_892, B_893)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56936, c_48834])).
% 16.27/8.51  tff(c_57008, plain, (![A_895, B_896]: (k4_xboole_0(A_895, k2_xboole_0(B_896, A_895))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56949])).
% 16.27/8.51  tff(c_57093, plain, (![B_900, A_901]: (k4_xboole_0(B_900, k2_xboole_0(B_900, A_901))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_57008])).
% 16.27/8.51  tff(c_57114, plain, (![B_900, A_901]: (k3_xboole_0(B_900, k2_xboole_0(B_900, A_901))=k4_xboole_0(B_900, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_57093, c_28])).
% 16.27/8.51  tff(c_57153, plain, (![B_900, A_901]: (k3_xboole_0(B_900, k2_xboole_0(B_900, A_901))=B_900)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_57114])).
% 16.27/8.51  tff(c_56306, plain, (![B_21, A_20]: (k2_xboole_0(B_21, k4_xboole_0(A_20, B_21))=k2_xboole_0(B_21, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_56280])).
% 16.27/8.51  tff(c_56830, plain, (![B_887, A_888]: (k2_xboole_0(B_887, k2_xboole_0(A_888, B_887))=k2_xboole_0(B_887, A_888))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56306])).
% 16.27/8.51  tff(c_56871, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_56830])).
% 16.27/8.51  tff(c_59582, plain, (![A_965, B_966]: (k4_xboole_0(k2_xboole_0(A_965, B_966), k4_xboole_0(B_966, A_965))=k4_xboole_0(A_965, k4_xboole_0(B_966, A_965)))), inference(superposition, [status(thm), theory('equality')], [c_56280, c_24])).
% 16.27/8.51  tff(c_59642, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k4_xboole_0(k2_xboole_0(A_1, B_2), A_1))=k4_xboole_0(A_1, k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)))), inference(superposition, [status(thm), theory('equality')], [c_56871, c_59582])).
% 16.27/8.51  tff(c_59724, plain, (![A_967, B_968]: (k4_xboole_0(A_967, k4_xboole_0(B_968, A_967))=A_967)), inference(demodulation, [status(thm), theory('equality')], [c_48707, c_57153, c_4, c_28, c_59642])).
% 16.27/8.51  tff(c_59753, plain, (![A_967, B_968]: (k3_xboole_0(A_967, k4_xboole_0(B_968, A_967))=k4_xboole_0(A_967, A_967))), inference(superposition, [status(thm), theory('equality')], [c_59724, c_28])).
% 16.27/8.51  tff(c_59847, plain, (![A_969, B_970]: (k3_xboole_0(A_969, k4_xboole_0(B_970, A_969))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48834, c_59753])).
% 16.27/8.51  tff(c_56754, plain, (![A_884, B_885]: (r2_hidden('#skF_2'(A_884, B_885), k3_xboole_0(A_884, B_885)) | r1_xboole_0(A_884, B_885))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_56787, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4), k3_xboole_0(B_4, A_3)) | r1_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_56754])).
% 16.27/8.51  tff(c_59867, plain, (![B_970, A_969]: (r2_hidden('#skF_2'(k4_xboole_0(B_970, A_969), A_969), k1_xboole_0) | r1_xboole_0(k4_xboole_0(B_970, A_969), A_969))), inference(superposition, [status(thm), theory('equality')], [c_59847, c_56787])).
% 16.27/8.51  tff(c_60103, plain, (![B_973, A_974]: (r1_xboole_0(k4_xboole_0(B_973, A_974), A_974))), inference(negUnitSimplification, [status(thm)], [c_48867, c_59867])).
% 16.27/8.51  tff(c_60149, plain, (![A_22, B_23, C_24]: (r1_xboole_0(k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)), C_24))), inference(superposition, [status(thm), theory('equality')], [c_26, c_60103])).
% 16.27/8.51  tff(c_62850, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_62523, c_60149])).
% 16.27/8.51  tff(c_62890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56248, c_62850])).
% 16.27/8.51  tff(c_62892, plain, (~r1_xboole_0('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_32])).
% 16.27/8.51  tff(c_34, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.27/8.51  tff(c_62923, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62892, c_34])).
% 16.27/8.51  tff(c_62924, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_62923])).
% 16.27/8.51  tff(c_62930, plain, (![A_1011, B_1012]: (k4_xboole_0(k2_xboole_0(A_1011, B_1012), B_1012)=k4_xboole_0(A_1011, B_1012))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.27/8.51  tff(c_62940, plain, (![A_1011]: (k4_xboole_0(A_1011, k1_xboole_0)=k2_xboole_0(A_1011, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62930, c_22])).
% 16.27/8.51  tff(c_62959, plain, (![A_1011]: (k2_xboole_0(A_1011, k1_xboole_0)=A_1011)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_62940])).
% 16.27/8.51  tff(c_62952, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_62930])).
% 16.27/8.51  tff(c_62990, plain, (![A_1014, B_1015]: (k4_xboole_0(A_1014, k4_xboole_0(A_1014, B_1015))=k3_xboole_0(A_1014, B_1015))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.27/8.51  tff(c_63011, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_62990])).
% 16.27/8.51  tff(c_63016, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_63011])).
% 16.27/8.51  tff(c_63618, plain, (![A_1053, B_1054, C_1055]: (k4_xboole_0(k4_xboole_0(A_1053, B_1054), C_1055)=k4_xboole_0(A_1053, k2_xboole_0(B_1054, C_1055)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.27/8.51  tff(c_70021, plain, (![C_1205, A_1206, B_1207]: (k2_xboole_0(C_1205, k4_xboole_0(A_1206, k2_xboole_0(B_1207, C_1205)))=k2_xboole_0(C_1205, k4_xboole_0(A_1206, B_1207)))), inference(superposition, [status(thm), theory('equality')], [c_63618, c_20])).
% 16.27/8.51  tff(c_70256, plain, (![C_1205, B_1207]: (k2_xboole_0(C_1205, k4_xboole_0(k2_xboole_0(B_1207, C_1205), B_1207))=k2_xboole_0(C_1205, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_63016, c_70021])).
% 16.27/8.51  tff(c_70327, plain, (![C_1208, B_1209]: (k2_xboole_0(C_1208, k4_xboole_0(C_1208, B_1209))=C_1208)), inference(demodulation, [status(thm), theory('equality')], [c_62952, c_62959, c_70256])).
% 16.27/8.51  tff(c_63017, plain, (![A_1016]: (k4_xboole_0(A_1016, A_1016)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_63011])).
% 16.27/8.51  tff(c_63022, plain, (![A_1016]: (k4_xboole_0(A_1016, k1_xboole_0)=k3_xboole_0(A_1016, A_1016))), inference(superposition, [status(thm), theory('equality')], [c_63017, c_28])).
% 16.27/8.51  tff(c_63037, plain, (![A_1016]: (k3_xboole_0(A_1016, A_1016)=A_1016)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_63022])).
% 16.27/8.51  tff(c_63202, plain, (![A_1023, B_1024, C_1025]: (~r1_xboole_0(A_1023, B_1024) | ~r2_hidden(C_1025, k3_xboole_0(A_1023, B_1024)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_63254, plain, (![A_1028, C_1029]: (~r1_xboole_0(A_1028, A_1028) | ~r2_hidden(C_1029, A_1028))), inference(superposition, [status(thm), theory('equality')], [c_63037, c_63202])).
% 16.27/8.51  tff(c_63260, plain, (![C_1029, B_6]: (~r2_hidden(C_1029, B_6) | k3_xboole_0(B_6, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_63254])).
% 16.27/8.51  tff(c_63269, plain, (![C_1030, B_1031]: (~r2_hidden(C_1030, B_1031) | k1_xboole_0!=B_1031)), inference(demodulation, [status(thm), theory('equality')], [c_63037, c_63260])).
% 16.27/8.51  tff(c_63312, plain, (![B_1037, A_1038]: (k1_xboole_0!=B_1037 | r1_xboole_0(A_1038, B_1037))), inference(resolution, [status(thm)], [c_12, c_63269])).
% 16.27/8.51  tff(c_63331, plain, (![A_1038, B_1037]: (k3_xboole_0(A_1038, B_1037)=k1_xboole_0 | k1_xboole_0!=B_1037)), inference(resolution, [status(thm)], [c_63312, c_6])).
% 16.27/8.51  tff(c_63628, plain, (![A_1053, B_1054]: (k4_xboole_0(A_1053, k2_xboole_0(B_1054, k4_xboole_0(A_1053, B_1054)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63618, c_63016])).
% 16.27/8.51  tff(c_63690, plain, (![A_1056, B_1057]: (k4_xboole_0(A_1056, k2_xboole_0(B_1057, A_1056))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_63628])).
% 16.27/8.51  tff(c_63705, plain, (![A_1056, B_1057]: (k3_xboole_0(A_1056, k2_xboole_0(B_1057, A_1056))=k4_xboole_0(A_1056, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_63690, c_28])).
% 16.27/8.51  tff(c_63747, plain, (![A_1058, B_1059]: (k3_xboole_0(A_1058, k2_xboole_0(B_1059, A_1058))=A_1058)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_63705])).
% 16.27/8.51  tff(c_63772, plain, (![A_1038, B_1059]: (k1_xboole_0=A_1038 | k2_xboole_0(B_1059, A_1038)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63331, c_63747])).
% 16.27/8.51  tff(c_71949, plain, (![C_1220, B_1221]: (k4_xboole_0(C_1220, B_1221)=k1_xboole_0 | k1_xboole_0!=C_1220)), inference(superposition, [status(thm), theory('equality')], [c_70327, c_63772])).
% 16.27/8.51  tff(c_72114, plain, (![B_1221, C_1220]: (k2_xboole_0(B_1221, k1_xboole_0)=k2_xboole_0(B_1221, C_1220) | k1_xboole_0!=C_1220)), inference(superposition, [status(thm), theory('equality')], [c_71949, c_20])).
% 16.27/8.51  tff(c_72429, plain, (![B_1221]: (k2_xboole_0(B_1221, k1_xboole_0)=B_1221)), inference(demodulation, [status(thm), theory('equality')], [c_62959, c_72114])).
% 16.27/8.51  tff(c_62962, plain, (![A_1013]: (k2_xboole_0(A_1013, k1_xboole_0)=A_1013)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_62940])).
% 16.27/8.51  tff(c_62974, plain, (![A_1013]: (k2_xboole_0(k1_xboole_0, A_1013)=A_1013)), inference(superposition, [status(thm), theory('equality')], [c_62962, c_2])).
% 16.27/8.51  tff(c_63732, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_63690])).
% 16.27/8.51  tff(c_62891, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_32])).
% 16.27/8.51  tff(c_62903, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_62891, c_6])).
% 16.27/8.51  tff(c_62999, plain, (![A_1014, B_1015]: (k2_xboole_0(k4_xboole_0(A_1014, B_1015), k3_xboole_0(A_1014, B_1015))=k2_xboole_0(k4_xboole_0(A_1014, B_1015), A_1014))), inference(superposition, [status(thm), theory('equality')], [c_62990, c_20])).
% 16.27/8.51  tff(c_69077, plain, (![A_1199, B_1200]: (k2_xboole_0(k4_xboole_0(A_1199, B_1200), k3_xboole_0(A_1199, B_1200))=k2_xboole_0(A_1199, k4_xboole_0(A_1199, B_1200)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62999])).
% 16.27/8.51  tff(c_69297, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_xboole_0)=k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_62903, c_69077])).
% 16.27/8.51  tff(c_69363, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62959, c_69297])).
% 16.27/8.51  tff(c_63791, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k2_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_63747])).
% 16.27/8.51  tff(c_64135, plain, (![A_1077, B_1078]: (k4_xboole_0(k2_xboole_0(A_1077, B_1078), A_1077)=k4_xboole_0(B_1078, A_1077))), inference(superposition, [status(thm), theory('equality')], [c_2, c_62930])).
% 16.27/8.51  tff(c_64144, plain, (![A_1077, B_1078]: (k4_xboole_0(k2_xboole_0(A_1077, B_1078), k4_xboole_0(B_1078, A_1077))=k3_xboole_0(k2_xboole_0(A_1077, B_1078), A_1077))), inference(superposition, [status(thm), theory('equality')], [c_64135, c_28])).
% 16.27/8.51  tff(c_64190, plain, (![A_1077, B_1078]: (k4_xboole_0(k2_xboole_0(A_1077, B_1078), k4_xboole_0(B_1078, A_1077))=A_1077)), inference(demodulation, [status(thm), theory('equality')], [c_63791, c_4, c_64144])).
% 16.27/8.51  tff(c_69632, plain, (k4_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k4_xboole_0(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_69363, c_64190])).
% 16.27/8.51  tff(c_69711, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62974, c_2, c_63732, c_26, c_2, c_26, c_69632])).
% 16.27/8.51  tff(c_70432, plain, (![C_1208, B_1209]: (k4_xboole_0(k4_xboole_0(C_1208, B_1209), C_1208)=k4_xboole_0(C_1208, C_1208))), inference(superposition, [status(thm), theory('equality')], [c_70327, c_62952])).
% 16.27/8.51  tff(c_70573, plain, (![C_1208, B_1209]: (k4_xboole_0(k4_xboole_0(C_1208, B_1209), C_1208)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63016, c_70432])).
% 16.27/8.51  tff(c_71073, plain, (![A_1214, B_1215, C_1216]: (k4_xboole_0(k4_xboole_0(A_1214, B_1215), k4_xboole_0(A_1214, k2_xboole_0(B_1215, C_1216)))=k3_xboole_0(k4_xboole_0(A_1214, B_1215), C_1216))), inference(superposition, [status(thm), theory('equality')], [c_63618, c_28])).
% 16.27/8.51  tff(c_71158, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_69711, c_71073])).
% 16.27/8.51  tff(c_71355, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70573, c_4, c_71158])).
% 16.27/8.51  tff(c_16, plain, (![A_12, B_13]: (r2_hidden('#skF_2'(A_12, B_13), k3_xboole_0(A_12, B_13)) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_63488, plain, (![B_1046, A_1047, C_1048]: (~r1_xboole_0(B_1046, A_1047) | ~r2_hidden(C_1048, k3_xboole_0(A_1047, B_1046)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_63202])).
% 16.27/8.51  tff(c_63521, plain, (![B_1049, A_1050]: (~r1_xboole_0(B_1049, A_1050) | r1_xboole_0(A_1050, B_1049))), inference(resolution, [status(thm)], [c_16, c_63488])).
% 16.27/8.51  tff(c_63594, plain, (![B_1051, A_1052]: (r1_xboole_0(B_1051, A_1052) | k3_xboole_0(A_1052, B_1051)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_63521])).
% 16.27/8.51  tff(c_63617, plain, (![B_1051, A_1052]: (k3_xboole_0(B_1051, A_1052)=k1_xboole_0 | k3_xboole_0(A_1052, B_1051)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_63594, c_6])).
% 16.27/8.51  tff(c_71479, plain, (k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_71355, c_63617])).
% 16.27/8.51  tff(c_71312, plain, (![B_1215, C_1216]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_1215, C_1216), B_1215), k1_xboole_0)=k3_xboole_0(k4_xboole_0(k2_xboole_0(B_1215, C_1216), B_1215), C_1216))), inference(superposition, [status(thm), theory('equality')], [c_63016, c_71073])).
% 16.27/8.51  tff(c_71402, plain, (![C_1216, B_1215]: (k3_xboole_0(C_1216, k4_xboole_0(C_1216, B_1215))=k4_xboole_0(C_1216, B_1215))), inference(demodulation, [status(thm), theory('equality')], [c_62952, c_4, c_62952, c_22, c_71312])).
% 16.27/8.51  tff(c_63002, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k3_xboole_0(A_25, k4_xboole_0(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_62990])).
% 16.27/8.51  tff(c_75047, plain, (![A_1247, B_1248]: (k4_xboole_0(A_1247, k3_xboole_0(A_1247, B_1248))=k4_xboole_0(A_1247, B_1248))), inference(demodulation, [status(thm), theory('equality')], [c_71402, c_63002])).
% 16.27/8.51  tff(c_75153, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_71479, c_75047])).
% 16.27/8.51  tff(c_75222, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72429, c_69711, c_26, c_26, c_75153])).
% 16.27/8.51  tff(c_63216, plain, (![C_1025]: (~r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r2_hidden(C_1025, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62903, c_63202])).
% 16.27/8.51  tff(c_63232, plain, (![C_1025]: (~r2_hidden(C_1025, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_62891, c_63216])).
% 16.27/8.51  tff(c_62946, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), k4_xboole_0(B_18, A_17))=k4_xboole_0(A_17, k4_xboole_0(B_18, A_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_62930])).
% 16.27/8.51  tff(c_68276, plain, (![A_1189, B_1190]: (k4_xboole_0(A_1189, k4_xboole_0(B_1190, A_1189))=A_1189)), inference(demodulation, [status(thm), theory('equality')], [c_64190, c_62946])).
% 16.27/8.51  tff(c_68311, plain, (![A_1189, B_1190]: (k3_xboole_0(A_1189, k4_xboole_0(B_1190, A_1189))=k4_xboole_0(A_1189, A_1189))), inference(superposition, [status(thm), theory('equality')], [c_68276, c_28])).
% 16.27/8.51  tff(c_68700, plain, (![A_1193, B_1194]: (k3_xboole_0(A_1193, k4_xboole_0(B_1194, A_1193))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63016, c_68311])).
% 16.27/8.51  tff(c_63446, plain, (![A_1043, B_1044]: (r2_hidden('#skF_2'(A_1043, B_1044), k3_xboole_0(A_1043, B_1044)) | r1_xboole_0(A_1043, B_1044))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.27/8.51  tff(c_63470, plain, (![B_4, A_3]: (r2_hidden('#skF_2'(B_4, A_3), k3_xboole_0(A_3, B_4)) | r1_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_63446])).
% 16.27/8.51  tff(c_68728, plain, (![B_1194, A_1193]: (r2_hidden('#skF_2'(k4_xboole_0(B_1194, A_1193), A_1193), k1_xboole_0) | r1_xboole_0(k4_xboole_0(B_1194, A_1193), A_1193))), inference(superposition, [status(thm), theory('equality')], [c_68700, c_63470])).
% 16.27/8.51  tff(c_68843, plain, (![B_1194, A_1193]: (r1_xboole_0(k4_xboole_0(B_1194, A_1193), A_1193))), inference(negUnitSimplification, [status(thm)], [c_63232, c_68728])).
% 16.27/8.51  tff(c_75280, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_75222, c_68843])).
% 16.27/8.51  tff(c_75330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62924, c_75280])).
% 16.27/8.51  tff(c_75331, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_62923])).
% 16.27/8.51  tff(c_75336, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_75331])).
% 16.27/8.51  tff(c_75579, plain, (![A_1267, B_1268]: (k4_xboole_0(k2_xboole_0(A_1267, B_1268), B_1268)=k4_xboole_0(A_1267, B_1268))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.27/8.51  tff(c_75607, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75579])).
% 16.27/8.51  tff(c_75592, plain, (![A_1267]: (k4_xboole_0(A_1267, k1_xboole_0)=k2_xboole_0(A_1267, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_75579, c_22])).
% 16.27/8.51  tff(c_75618, plain, (![A_1267]: (k2_xboole_0(A_1267, k1_xboole_0)=A_1267)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_75592])).
% 16.27/8.51  tff(c_75426, plain, (![A_1256, B_1257]: (k4_xboole_0(A_1256, k4_xboole_0(A_1256, B_1257))=k3_xboole_0(A_1256, B_1257))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.27/8.51  tff(c_75444, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_75426])).
% 16.27/8.51  tff(c_75448, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_75444])).
% 16.27/8.51  tff(c_75798, plain, (![A_1276, B_1277, C_1278]: (k4_xboole_0(k4_xboole_0(A_1276, B_1277), C_1278)=k4_xboole_0(A_1276, k2_xboole_0(B_1277, C_1278)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.27/8.51  tff(c_78913, plain, (![C_1387, A_1388, B_1389]: (k2_xboole_0(C_1387, k4_xboole_0(A_1388, k2_xboole_0(B_1389, C_1387)))=k2_xboole_0(C_1387, k4_xboole_0(A_1388, B_1389)))), inference(superposition, [status(thm), theory('equality')], [c_75798, c_20])).
% 16.27/8.51  tff(c_79051, plain, (![C_1387, B_1389]: (k2_xboole_0(C_1387, k4_xboole_0(k2_xboole_0(B_1389, C_1387), B_1389))=k2_xboole_0(C_1387, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_75448, c_78913])).
% 16.27/8.51  tff(c_79091, plain, (![C_1387, B_1389]: (k2_xboole_0(C_1387, k4_xboole_0(C_1387, B_1389))=C_1387)), inference(demodulation, [status(thm), theory('equality')], [c_75607, c_75618, c_79051])).
% 16.27/8.51  tff(c_75332, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_62923])).
% 16.27/8.51  tff(c_75340, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_75332, c_6])).
% 16.27/8.51  tff(c_77975, plain, (![A_1364, B_1365]: (k4_xboole_0(A_1364, k3_xboole_0(A_1364, B_1365))=k3_xboole_0(A_1364, k4_xboole_0(A_1364, B_1365)))), inference(superposition, [status(thm), theory('equality')], [c_75426, c_28])).
% 16.27/8.51  tff(c_78033, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75340, c_77975])).
% 16.27/8.51  tff(c_78058, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_78033])).
% 16.27/8.51  tff(c_79092, plain, (![C_1390, B_1391]: (k2_xboole_0(C_1390, k4_xboole_0(C_1390, B_1391))=C_1390)), inference(demodulation, [status(thm), theory('equality')], [c_75607, c_75618, c_79051])).
% 16.27/8.51  tff(c_79263, plain, (![A_1392, B_1393]: (k2_xboole_0(A_1392, k3_xboole_0(A_1392, B_1393))=A_1392)), inference(superposition, [status(thm), theory('equality')], [c_28, c_79092])).
% 16.27/8.51  tff(c_79852, plain, (![B_1400, A_1401]: (k2_xboole_0(B_1400, k3_xboole_0(A_1401, B_1400))=B_1400)), inference(superposition, [status(thm), theory('equality')], [c_4, c_79263])).
% 16.27/8.51  tff(c_75808, plain, (![A_1276, B_1277]: (k4_xboole_0(A_1276, k2_xboole_0(B_1277, k4_xboole_0(A_1276, B_1277)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75798, c_75448])).
% 16.27/8.51  tff(c_75858, plain, (![A_1276, B_1277]: (k4_xboole_0(A_1276, k2_xboole_0(B_1277, A_1276))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_75808])).
% 16.27/8.51  tff(c_80025, plain, (![A_1402, B_1403]: (k4_xboole_0(k3_xboole_0(A_1402, B_1403), B_1403)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79852, c_75858])).
% 16.27/8.51  tff(c_80094, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_78058, c_80025])).
% 16.27/8.51  tff(c_75914, plain, (![A_1283, B_1284]: (k4_xboole_0(A_1283, k2_xboole_0(B_1284, A_1283))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_75808])).
% 16.27/8.51  tff(c_75929, plain, (![A_1283, B_1284]: (k3_xboole_0(A_1283, k2_xboole_0(B_1284, A_1283))=k4_xboole_0(A_1283, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_75914, c_28])).
% 16.27/8.51  tff(c_75963, plain, (![A_1283, B_1284]: (k3_xboole_0(A_1283, k2_xboole_0(B_1284, A_1283))=A_1283)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_75929])).
% 16.27/8.51  tff(c_75585, plain, (![A_1267, B_1268]: (k4_xboole_0(k2_xboole_0(A_1267, B_1268), k4_xboole_0(A_1267, B_1268))=k3_xboole_0(k2_xboole_0(A_1267, B_1268), B_1268))), inference(superposition, [status(thm), theory('equality')], [c_75579, c_28])).
% 16.27/8.51  tff(c_75616, plain, (![A_1267, B_1268]: (k4_xboole_0(k2_xboole_0(A_1267, B_1268), k4_xboole_0(A_1267, B_1268))=k3_xboole_0(B_1268, k2_xboole_0(A_1267, B_1268)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_75585])).
% 16.27/8.51  tff(c_79682, plain, (![A_1267, B_1268]: (k4_xboole_0(k2_xboole_0(A_1267, B_1268), k4_xboole_0(A_1267, B_1268))=B_1268)), inference(demodulation, [status(thm), theory('equality')], [c_75963, c_75616])).
% 16.27/8.51  tff(c_80383, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4')), k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_80094, c_79682])).
% 16.27/8.51  tff(c_80426, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_79091, c_80383])).
% 16.27/8.51  tff(c_78036, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62903, c_77975])).
% 16.27/8.51  tff(c_78059, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_78036])).
% 16.27/8.51  tff(c_80091, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_78059, c_80025])).
% 16.27/8.51  tff(c_80447, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), k1_xboole_0)=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_80091, c_79682])).
% 16.27/8.51  tff(c_80490, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_79091, c_80447])).
% 16.27/8.51  tff(c_75848, plain, (![A_1276, B_1277, B_26]: (k4_xboole_0(A_1276, k2_xboole_0(B_1277, k4_xboole_0(k4_xboole_0(A_1276, B_1277), B_26)))=k3_xboole_0(k4_xboole_0(A_1276, B_1277), B_26))), inference(superposition, [status(thm), theory('equality')], [c_28, c_75798])).
% 16.27/8.51  tff(c_83041, plain, (![A_1430, B_1431, B_1432]: (k4_xboole_0(A_1430, k2_xboole_0(B_1431, k4_xboole_0(A_1430, k2_xboole_0(B_1431, B_1432))))=k3_xboole_0(k4_xboole_0(A_1430, B_1431), B_1432))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_75848])).
% 16.27/8.51  tff(c_83182, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_80490, c_83041])).
% 16.27/8.51  tff(c_83313, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_80426, c_75858, c_4, c_83182])).
% 16.27/8.51  tff(c_83315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75336, c_83313])).
% 16.27/8.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.27/8.51  
% 16.27/8.51  Inference rules
% 16.27/8.51  ----------------------
% 16.27/8.51  #Ref     : 4
% 16.27/8.51  #Sup     : 21669
% 16.27/8.51  #Fact    : 0
% 16.27/8.51  #Define  : 0
% 16.27/8.51  #Split   : 59
% 16.27/8.51  #Chain   : 0
% 16.27/8.51  #Close   : 0
% 16.27/8.51  
% 16.27/8.51  Ordering : KBO
% 16.27/8.51  
% 16.27/8.51  Simplification rules
% 16.27/8.51  ----------------------
% 16.27/8.51  #Subsume      : 3627
% 16.27/8.51  #Demod        : 18507
% 16.27/8.51  #Tautology    : 11714
% 16.27/8.51  #SimpNegUnit  : 593
% 16.27/8.51  #BackRed      : 118
% 16.27/8.51  
% 16.27/8.51  #Partial instantiations: 0
% 16.27/8.51  #Strategies tried      : 1
% 16.27/8.51  
% 16.27/8.51  Timing (in seconds)
% 16.27/8.51  ----------------------
% 16.27/8.51  Preprocessing        : 0.29
% 16.27/8.51  Parsing              : 0.16
% 16.27/8.51  CNF conversion       : 0.02
% 16.27/8.51  Main loop            : 7.35
% 16.27/8.51  Inferencing          : 1.38
% 16.27/8.51  Reduction            : 4.22
% 16.27/8.51  Demodulation         : 3.62
% 16.27/8.51  BG Simplification    : 0.16
% 16.27/8.51  Subsumption          : 1.26
% 16.27/8.51  Abstraction          : 0.29
% 16.27/8.51  MUC search           : 0.00
% 16.27/8.51  Cooper               : 0.00
% 16.27/8.51  Total                : 7.78
% 16.27/8.51  Index Insertion      : 0.00
% 16.27/8.51  Index Deletion       : 0.00
% 16.27/8.51  Index Matching       : 0.00
% 16.27/8.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
