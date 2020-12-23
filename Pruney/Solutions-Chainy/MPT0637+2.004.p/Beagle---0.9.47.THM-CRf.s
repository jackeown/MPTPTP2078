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
% DateTime   : Thu Dec  3 10:03:24 EST 2020

% Result     : Theorem 11.19s
% Output     : CNFRefutation 11.45s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 409 expanded)
%              Number of leaves         :   30 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  209 ( 729 expanded)
%              Number of equality atoms :   70 ( 250 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_362,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,k3_xboole_0(k1_relat_1(B_74),A_75)) = k7_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_213,plain,(
    ! [A_59,B_60] :
      ( k5_relat_1(k6_relat_1(A_59),B_60) = k7_relat_1(B_60,A_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k5_relat_1(B_28,k6_relat_1(A_27)),B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_220,plain,(
    ! [A_27,A_59] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_27),A_59),k6_relat_1(A_59))
      | ~ v1_relat_1(k6_relat_1(A_59))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_32])).

tff(c_235,plain,(
    ! [A_27,A_59] : r1_tarski(k7_relat_1(k6_relat_1(A_27),A_59),k6_relat_1(A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_220])).

tff(c_372,plain,(
    ! [A_27,A_75] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_27),A_75),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_27)),A_75)))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_235])).

tff(c_392,plain,(
    ! [A_27,A_75] : r1_tarski(k7_relat_1(k6_relat_1(A_27),A_75),k6_relat_1(k3_xboole_0(A_27,A_75))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_26,c_372])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_257,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(k6_relat_1(A_69),B_70) = B_70
      | ~ r1_tarski(k1_relat_1(B_70),A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_268,plain,(
    ! [B_71] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_71)),B_71) = B_71
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_294,plain,(
    ! [A_26] :
      ( k5_relat_1(k6_relat_1(A_26),k6_relat_1(A_26)) = k6_relat_1(A_26)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_268])).

tff(c_304,plain,(
    ! [A_72] : k5_relat_1(k6_relat_1(A_72),k6_relat_1(A_72)) = k6_relat_1(A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_294])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( k5_relat_1(k6_relat_1(A_31),B_32) = k7_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_310,plain,(
    ! [A_72] :
      ( k7_relat_1(k6_relat_1(A_72),A_72) = k6_relat_1(A_72)
      | ~ v1_relat_1(k6_relat_1(A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_36])).

tff(c_329,plain,(
    ! [A_72] : k7_relat_1(k6_relat_1(A_72),A_72) = k6_relat_1(A_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_310])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_260,plain,(
    ! [A_69,A_26] :
      ( k5_relat_1(k6_relat_1(A_69),k6_relat_1(A_26)) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_69)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_257])).

tff(c_675,plain,(
    ! [A_100,A_101] :
      ( k5_relat_1(k6_relat_1(A_100),k6_relat_1(A_101)) = k6_relat_1(A_101)
      | ~ r1_tarski(A_101,A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_260])).

tff(c_718,plain,(
    ! [A_101,A_31] :
      ( k7_relat_1(k6_relat_1(A_101),A_31) = k6_relat_1(A_101)
      | ~ r1_tarski(A_101,A_31)
      | ~ v1_relat_1(k6_relat_1(A_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_675])).

tff(c_750,plain,(
    ! [A_104,A_105] :
      ( k7_relat_1(k6_relat_1(A_104),A_105) = k6_relat_1(A_104)
      | ~ r1_tarski(A_104,A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_718])).

tff(c_771,plain,(
    ! [A_104,A_105] :
      ( r1_tarski(k6_relat_1(A_104),k6_relat_1(k3_xboole_0(A_104,A_105)))
      | ~ r1_tarski(A_104,A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_392])).

tff(c_695,plain,(
    ! [A_101,A_100] :
      ( r1_tarski(k6_relat_1(A_101),k6_relat_1(A_100))
      | ~ v1_relat_1(k6_relat_1(A_100))
      | ~ r1_tarski(A_101,A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_32])).

tff(c_746,plain,(
    ! [A_102,A_103] :
      ( r1_tarski(k6_relat_1(A_102),k6_relat_1(A_103))
      | ~ r1_tarski(A_102,A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_695])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1340,plain,(
    ! [A_132,A_131] :
      ( k6_relat_1(A_132) = k6_relat_1(A_131)
      | ~ r1_tarski(k6_relat_1(A_131),k6_relat_1(A_132))
      | ~ r1_tarski(A_132,A_131) ) ),
    inference(resolution,[status(thm)],[c_746,c_2])).

tff(c_1349,plain,(
    ! [A_104,A_105] :
      ( k6_relat_1(k3_xboole_0(A_104,A_105)) = k6_relat_1(A_104)
      | ~ r1_tarski(k3_xboole_0(A_104,A_105),A_104)
      | ~ r1_tarski(A_104,A_105) ) ),
    inference(resolution,[status(thm)],[c_771,c_1340])).

tff(c_1875,plain,(
    ! [A_144,A_145] :
      ( k6_relat_1(k3_xboole_0(A_144,A_145)) = k6_relat_1(A_144)
      | ~ r1_tarski(A_144,A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1349])).

tff(c_1985,plain,(
    ! [A_144,A_145] :
      ( k3_xboole_0(A_144,A_145) = k1_relat_1(k6_relat_1(A_144))
      | ~ r1_tarski(A_144,A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1875,c_26])).

tff(c_2020,plain,(
    ! [A_146,A_147] :
      ( k3_xboole_0(A_146,A_147) = A_146
      | ~ r1_tarski(A_146,A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1985])).

tff(c_2203,plain,(
    ! [A_150,B_151] : k3_xboole_0(k3_xboole_0(A_150,B_151),A_150) = k3_xboole_0(A_150,B_151) ),
    inference(resolution,[status(thm)],[c_8,c_2020])).

tff(c_389,plain,(
    ! [A_26,A_75] :
      ( k7_relat_1(k6_relat_1(A_26),k3_xboole_0(A_26,A_75)) = k7_relat_1(k6_relat_1(A_26),A_75)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_362])).

tff(c_395,plain,(
    ! [A_26,A_75] : k7_relat_1(k6_relat_1(A_26),k3_xboole_0(A_26,A_75)) = k7_relat_1(k6_relat_1(A_26),A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_389])).

tff(c_2248,plain,(
    ! [A_150,B_151] : k7_relat_1(k6_relat_1(k3_xboole_0(A_150,B_151)),k3_xboole_0(A_150,B_151)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_150,B_151)),A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_395])).

tff(c_2324,plain,(
    ! [A_150,B_151] : k7_relat_1(k6_relat_1(k3_xboole_0(A_150,B_151)),A_150) = k6_relat_1(k3_xboole_0(A_150,B_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_2248])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,k3_xboole_0(k1_relat_1(B_18),A_17)) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_591,plain,(
    ! [A_94,A_95] : k7_relat_1(k6_relat_1(A_94),k3_xboole_0(A_94,A_95)) = k7_relat_1(k6_relat_1(A_94),A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_389])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k5_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_223,plain,(
    ! [B_60,A_59] :
      ( v1_relat_1(k7_relat_1(B_60,A_59))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k6_relat_1(A_59))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_16])).

tff(c_237,plain,(
    ! [B_60,A_59] :
      ( v1_relat_1(k7_relat_1(B_60,A_59))
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_223])).

tff(c_612,plain,(
    ! [A_94,A_95] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_94),A_95))
      | ~ v1_relat_1(k6_relat_1(A_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_237])).

tff(c_630,plain,(
    ! [A_94,A_95] : v1_relat_1(k7_relat_1(k6_relat_1(A_94),A_95)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_612])).

tff(c_303,plain,(
    ! [A_26] : k5_relat_1(k6_relat_1(A_26),k6_relat_1(A_26)) = k6_relat_1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_294])).

tff(c_531,plain,(
    ! [A_85,B_86,C_87] :
      ( k5_relat_1(k5_relat_1(A_85,B_86),C_87) = k5_relat_1(A_85,k5_relat_1(B_86,C_87))
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_559,plain,(
    ! [A_31,B_32,C_87] :
      ( k5_relat_1(k6_relat_1(A_31),k5_relat_1(B_32,C_87)) = k5_relat_1(k7_relat_1(B_32,A_31),C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_531])).

tff(c_1260,plain,(
    ! [A_126,B_127,C_128] :
      ( k5_relat_1(k6_relat_1(A_126),k5_relat_1(B_127,C_128)) = k5_relat_1(k7_relat_1(B_127,A_126),C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_559])).

tff(c_20395,plain,(
    ! [B_399,C_400,A_401] :
      ( k7_relat_1(k5_relat_1(B_399,C_400),A_401) = k5_relat_1(k7_relat_1(B_399,A_401),C_400)
      | ~ v1_relat_1(k5_relat_1(B_399,C_400))
      | ~ v1_relat_1(C_400)
      | ~ v1_relat_1(B_399) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1260,c_36])).

tff(c_20445,plain,(
    ! [A_26,A_401] :
      ( k7_relat_1(k5_relat_1(k6_relat_1(A_26),k6_relat_1(A_26)),A_401) = k5_relat_1(k7_relat_1(k6_relat_1(A_26),A_401),k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_20395])).

tff(c_20510,plain,(
    ! [A_402,A_403] : k5_relat_1(k7_relat_1(k6_relat_1(A_402),A_403),k6_relat_1(A_402)) = k7_relat_1(k6_relat_1(A_402),A_403) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_18,c_303,c_20445])).

tff(c_266,plain,(
    ! [A_69,A_26] :
      ( k5_relat_1(k6_relat_1(A_69),k6_relat_1(A_26)) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_260])).

tff(c_1294,plain,(
    ! [A_69,A_126,A_26] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_69),A_126),k6_relat_1(A_26)) = k5_relat_1(k6_relat_1(A_126),k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_69))
      | ~ r1_tarski(A_26,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_1260])).

tff(c_1326,plain,(
    ! [A_69,A_126,A_26] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_69),A_126),k6_relat_1(A_26)) = k5_relat_1(k6_relat_1(A_126),k6_relat_1(A_26))
      | ~ r1_tarski(A_26,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_1294])).

tff(c_20538,plain,(
    ! [A_403,A_402] :
      ( k5_relat_1(k6_relat_1(A_403),k6_relat_1(A_402)) = k7_relat_1(k6_relat_1(A_402),A_403)
      | ~ r1_tarski(A_402,A_402) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20510,c_1326])).

tff(c_20713,plain,(
    ! [A_403,A_402] : k5_relat_1(k6_relat_1(A_403),k6_relat_1(A_402)) = k7_relat_1(k6_relat_1(A_402),A_403) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20538])).

tff(c_453,plain,(
    ! [C_80,A_81,B_82] :
      ( k7_relat_1(k7_relat_1(C_80,A_81),B_82) = k7_relat_1(C_80,k3_xboole_0(A_81,B_82))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1608,plain,(
    ! [B_135,A_136,B_137] :
      ( k7_relat_1(B_135,k3_xboole_0(k3_xboole_0(k1_relat_1(B_135),A_136),B_137)) = k7_relat_1(k7_relat_1(B_135,A_136),B_137)
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_453])).

tff(c_10,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [B_45,A_46] : k1_setfam_1(k2_tarski(B_45,A_46)) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_14,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_124,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_14])).

tff(c_621,plain,(
    ! [B_45,A_46] : k7_relat_1(k6_relat_1(B_45),k3_xboole_0(A_46,B_45)) = k7_relat_1(k6_relat_1(B_45),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_591])).

tff(c_1626,plain,(
    ! [B_137,A_136] :
      ( k7_relat_1(k6_relat_1(B_137),k3_xboole_0(k1_relat_1(k6_relat_1(B_137)),A_136)) = k7_relat_1(k7_relat_1(k6_relat_1(B_137),A_136),B_137)
      | ~ v1_relat_1(k6_relat_1(B_137))
      | ~ v1_relat_1(k6_relat_1(B_137)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_621])).

tff(c_1714,plain,(
    ! [B_137,A_136] : k7_relat_1(k7_relat_1(k6_relat_1(B_137),A_136),B_137) = k7_relat_1(k6_relat_1(B_137),A_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_395,c_26,c_1626])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_27),B_28),B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_193,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_918,plain,(
    ! [A_108,B_109] :
      ( k5_relat_1(k6_relat_1(A_108),B_109) = B_109
      | ~ r1_tarski(B_109,k5_relat_1(k6_relat_1(A_108),B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_9000,plain,(
    ! [A_256,B_257] :
      ( k5_relat_1(k6_relat_1(A_256),B_257) = B_257
      | ~ r1_tarski(B_257,k7_relat_1(B_257,A_256))
      | ~ v1_relat_1(B_257)
      | ~ v1_relat_1(B_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_918])).

tff(c_9018,plain,(
    ! [B_137,A_136] :
      ( k5_relat_1(k6_relat_1(B_137),k7_relat_1(k6_relat_1(B_137),A_136)) = k7_relat_1(k6_relat_1(B_137),A_136)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(B_137),A_136),k7_relat_1(k6_relat_1(B_137),A_136))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_137),A_136))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_137),A_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_9000])).

tff(c_9064,plain,(
    ! [B_137,A_136] : k5_relat_1(k6_relat_1(B_137),k7_relat_1(k6_relat_1(B_137),A_136)) = k7_relat_1(k6_relat_1(B_137),A_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_630,c_6,c_9018])).

tff(c_541,plain,(
    ! [A_85,B_86,A_27] :
      ( r1_tarski(k5_relat_1(A_85,k5_relat_1(B_86,k6_relat_1(A_27))),k5_relat_1(A_85,B_86))
      | ~ v1_relat_1(k5_relat_1(A_85,B_86))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_32])).

tff(c_2466,plain,(
    ! [A_154,B_155,A_156] :
      ( r1_tarski(k5_relat_1(A_154,k5_relat_1(B_155,k6_relat_1(A_156))),k5_relat_1(A_154,B_155))
      | ~ v1_relat_1(k5_relat_1(A_154,B_155))
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_541])).

tff(c_2518,plain,(
    ! [A_154,A_156,A_31] :
      ( r1_tarski(k5_relat_1(A_154,k7_relat_1(k6_relat_1(A_156),A_31)),k5_relat_1(A_154,k6_relat_1(A_31)))
      | ~ v1_relat_1(k5_relat_1(A_154,k6_relat_1(A_31)))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(A_154)
      | ~ v1_relat_1(k6_relat_1(A_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2466])).

tff(c_24991,plain,(
    ! [A_444,A_445,A_446] :
      ( r1_tarski(k5_relat_1(A_444,k7_relat_1(k6_relat_1(A_445),A_446)),k5_relat_1(A_444,k6_relat_1(A_446)))
      | ~ v1_relat_1(k5_relat_1(A_444,k6_relat_1(A_446)))
      | ~ v1_relat_1(A_444) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_2518])).

tff(c_25004,plain,(
    ! [B_137,A_136] :
      ( r1_tarski(k7_relat_1(k6_relat_1(B_137),A_136),k5_relat_1(k6_relat_1(B_137),k6_relat_1(A_136)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(B_137),k6_relat_1(A_136)))
      | ~ v1_relat_1(k6_relat_1(B_137)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9064,c_24991])).

tff(c_25253,plain,(
    ! [B_447,A_448] : r1_tarski(k7_relat_1(k6_relat_1(B_447),A_448),k7_relat_1(k6_relat_1(A_448),B_447)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_630,c_20713,c_20713,c_25004])).

tff(c_25459,plain,(
    ! [A_448,A_17] :
      ( r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_448)),A_17)),A_448),k7_relat_1(k6_relat_1(A_448),A_17))
      | ~ v1_relat_1(k6_relat_1(A_448)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_25253])).

tff(c_27293,plain,(
    ! [A_465,A_466] : r1_tarski(k6_relat_1(k3_xboole_0(A_465,A_466)),k7_relat_1(k6_relat_1(A_465),A_466)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2324,c_26,c_25459])).

tff(c_27303,plain,(
    ! [A_465,A_466] :
      ( k7_relat_1(k6_relat_1(A_465),A_466) = k6_relat_1(k3_xboole_0(A_465,A_466))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_465),A_466),k6_relat_1(k3_xboole_0(A_465,A_466))) ) ),
    inference(resolution,[status(thm)],[c_27293,c_2])).

tff(c_27490,plain,(
    ! [A_465,A_466] : k7_relat_1(k6_relat_1(A_465),A_466) = k6_relat_1(k3_xboole_0(A_465,A_466)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_27303])).

tff(c_38,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_229,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_38])).

tff(c_239,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_229])).

tff(c_27599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27490,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.19/4.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.34/4.88  
% 11.34/4.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.34/4.88  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 11.34/4.88  
% 11.34/4.88  %Foreground sorts:
% 11.34/4.88  
% 11.34/4.88  
% 11.34/4.88  %Background operators:
% 11.34/4.88  
% 11.34/4.88  
% 11.34/4.88  %Foreground operators:
% 11.34/4.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.34/4.88  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.34/4.88  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.34/4.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.34/4.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.34/4.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.34/4.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.34/4.88  tff('#skF_2', type, '#skF_2': $i).
% 11.34/4.88  tff('#skF_1', type, '#skF_1': $i).
% 11.34/4.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.34/4.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.34/4.88  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.34/4.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.34/4.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.34/4.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.34/4.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.34/4.88  
% 11.45/4.90  tff(f_47, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 11.45/4.90  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.45/4.90  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 11.45/4.90  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 11.45/4.90  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 11.45/4.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.45/4.90  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 11.45/4.90  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.45/4.90  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 11.45/4.90  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 11.45/4.90  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 11.45/4.90  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.45/4.90  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.45/4.90  tff(f_88, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 11.45/4.90  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.45/4.90  tff(c_26, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.45/4.90  tff(c_362, plain, (![B_74, A_75]: (k7_relat_1(B_74, k3_xboole_0(k1_relat_1(B_74), A_75))=k7_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.45/4.90  tff(c_213, plain, (![A_59, B_60]: (k5_relat_1(k6_relat_1(A_59), B_60)=k7_relat_1(B_60, A_59) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.45/4.90  tff(c_32, plain, (![B_28, A_27]: (r1_tarski(k5_relat_1(B_28, k6_relat_1(A_27)), B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.45/4.90  tff(c_220, plain, (![A_27, A_59]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_59), k6_relat_1(A_59)) | ~v1_relat_1(k6_relat_1(A_59)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_32])).
% 11.45/4.90  tff(c_235, plain, (![A_27, A_59]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_59), k6_relat_1(A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_220])).
% 11.45/4.90  tff(c_372, plain, (![A_27, A_75]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_75), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_27)), A_75))) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_362, c_235])).
% 11.45/4.90  tff(c_392, plain, (![A_27, A_75]: (r1_tarski(k7_relat_1(k6_relat_1(A_27), A_75), k6_relat_1(k3_xboole_0(A_27, A_75))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_26, c_372])).
% 11.45/4.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.45/4.90  tff(c_257, plain, (![A_69, B_70]: (k5_relat_1(k6_relat_1(A_69), B_70)=B_70 | ~r1_tarski(k1_relat_1(B_70), A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.45/4.90  tff(c_268, plain, (![B_71]: (k5_relat_1(k6_relat_1(k1_relat_1(B_71)), B_71)=B_71 | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_6, c_257])).
% 11.45/4.90  tff(c_294, plain, (![A_26]: (k5_relat_1(k6_relat_1(A_26), k6_relat_1(A_26))=k6_relat_1(A_26) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_268])).
% 11.45/4.90  tff(c_304, plain, (![A_72]: (k5_relat_1(k6_relat_1(A_72), k6_relat_1(A_72))=k6_relat_1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_294])).
% 11.45/4.90  tff(c_36, plain, (![A_31, B_32]: (k5_relat_1(k6_relat_1(A_31), B_32)=k7_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.45/4.90  tff(c_310, plain, (![A_72]: (k7_relat_1(k6_relat_1(A_72), A_72)=k6_relat_1(A_72) | ~v1_relat_1(k6_relat_1(A_72)))), inference(superposition, [status(thm), theory('equality')], [c_304, c_36])).
% 11.45/4.90  tff(c_329, plain, (![A_72]: (k7_relat_1(k6_relat_1(A_72), A_72)=k6_relat_1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_310])).
% 11.45/4.90  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.45/4.90  tff(c_260, plain, (![A_69, A_26]: (k5_relat_1(k6_relat_1(A_69), k6_relat_1(A_26))=k6_relat_1(A_26) | ~r1_tarski(A_26, A_69) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_257])).
% 11.45/4.90  tff(c_675, plain, (![A_100, A_101]: (k5_relat_1(k6_relat_1(A_100), k6_relat_1(A_101))=k6_relat_1(A_101) | ~r1_tarski(A_101, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_260])).
% 11.45/4.90  tff(c_718, plain, (![A_101, A_31]: (k7_relat_1(k6_relat_1(A_101), A_31)=k6_relat_1(A_101) | ~r1_tarski(A_101, A_31) | ~v1_relat_1(k6_relat_1(A_101)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_675])).
% 11.45/4.90  tff(c_750, plain, (![A_104, A_105]: (k7_relat_1(k6_relat_1(A_104), A_105)=k6_relat_1(A_104) | ~r1_tarski(A_104, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_718])).
% 11.45/4.90  tff(c_771, plain, (![A_104, A_105]: (r1_tarski(k6_relat_1(A_104), k6_relat_1(k3_xboole_0(A_104, A_105))) | ~r1_tarski(A_104, A_105))), inference(superposition, [status(thm), theory('equality')], [c_750, c_392])).
% 11.45/4.90  tff(c_695, plain, (![A_101, A_100]: (r1_tarski(k6_relat_1(A_101), k6_relat_1(A_100)) | ~v1_relat_1(k6_relat_1(A_100)) | ~r1_tarski(A_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_675, c_32])).
% 11.45/4.90  tff(c_746, plain, (![A_102, A_103]: (r1_tarski(k6_relat_1(A_102), k6_relat_1(A_103)) | ~r1_tarski(A_102, A_103))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_695])).
% 11.45/4.90  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.45/4.90  tff(c_1340, plain, (![A_132, A_131]: (k6_relat_1(A_132)=k6_relat_1(A_131) | ~r1_tarski(k6_relat_1(A_131), k6_relat_1(A_132)) | ~r1_tarski(A_132, A_131))), inference(resolution, [status(thm)], [c_746, c_2])).
% 11.45/4.90  tff(c_1349, plain, (![A_104, A_105]: (k6_relat_1(k3_xboole_0(A_104, A_105))=k6_relat_1(A_104) | ~r1_tarski(k3_xboole_0(A_104, A_105), A_104) | ~r1_tarski(A_104, A_105))), inference(resolution, [status(thm)], [c_771, c_1340])).
% 11.45/4.90  tff(c_1875, plain, (![A_144, A_145]: (k6_relat_1(k3_xboole_0(A_144, A_145))=k6_relat_1(A_144) | ~r1_tarski(A_144, A_145))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1349])).
% 11.45/4.90  tff(c_1985, plain, (![A_144, A_145]: (k3_xboole_0(A_144, A_145)=k1_relat_1(k6_relat_1(A_144)) | ~r1_tarski(A_144, A_145))), inference(superposition, [status(thm), theory('equality')], [c_1875, c_26])).
% 11.45/4.90  tff(c_2020, plain, (![A_146, A_147]: (k3_xboole_0(A_146, A_147)=A_146 | ~r1_tarski(A_146, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1985])).
% 11.45/4.90  tff(c_2203, plain, (![A_150, B_151]: (k3_xboole_0(k3_xboole_0(A_150, B_151), A_150)=k3_xboole_0(A_150, B_151))), inference(resolution, [status(thm)], [c_8, c_2020])).
% 11.45/4.90  tff(c_389, plain, (![A_26, A_75]: (k7_relat_1(k6_relat_1(A_26), k3_xboole_0(A_26, A_75))=k7_relat_1(k6_relat_1(A_26), A_75) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_362])).
% 11.45/4.90  tff(c_395, plain, (![A_26, A_75]: (k7_relat_1(k6_relat_1(A_26), k3_xboole_0(A_26, A_75))=k7_relat_1(k6_relat_1(A_26), A_75))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_389])).
% 11.45/4.90  tff(c_2248, plain, (![A_150, B_151]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_150, B_151)), k3_xboole_0(A_150, B_151))=k7_relat_1(k6_relat_1(k3_xboole_0(A_150, B_151)), A_150))), inference(superposition, [status(thm), theory('equality')], [c_2203, c_395])).
% 11.45/4.90  tff(c_2324, plain, (![A_150, B_151]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_150, B_151)), A_150)=k6_relat_1(k3_xboole_0(A_150, B_151)))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_2248])).
% 11.45/4.90  tff(c_22, plain, (![B_18, A_17]: (k7_relat_1(B_18, k3_xboole_0(k1_relat_1(B_18), A_17))=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.45/4.90  tff(c_591, plain, (![A_94, A_95]: (k7_relat_1(k6_relat_1(A_94), k3_xboole_0(A_94, A_95))=k7_relat_1(k6_relat_1(A_94), A_95))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_389])).
% 11.45/4.90  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k5_relat_1(A_11, B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.45/4.90  tff(c_223, plain, (![B_60, A_59]: (v1_relat_1(k7_relat_1(B_60, A_59)) | ~v1_relat_1(B_60) | ~v1_relat_1(k6_relat_1(A_59)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_213, c_16])).
% 11.45/4.90  tff(c_237, plain, (![B_60, A_59]: (v1_relat_1(k7_relat_1(B_60, A_59)) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_223])).
% 11.45/4.90  tff(c_612, plain, (![A_94, A_95]: (v1_relat_1(k7_relat_1(k6_relat_1(A_94), A_95)) | ~v1_relat_1(k6_relat_1(A_94)))), inference(superposition, [status(thm), theory('equality')], [c_591, c_237])).
% 11.45/4.90  tff(c_630, plain, (![A_94, A_95]: (v1_relat_1(k7_relat_1(k6_relat_1(A_94), A_95)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_612])).
% 11.45/4.90  tff(c_303, plain, (![A_26]: (k5_relat_1(k6_relat_1(A_26), k6_relat_1(A_26))=k6_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_294])).
% 11.45/4.90  tff(c_531, plain, (![A_85, B_86, C_87]: (k5_relat_1(k5_relat_1(A_85, B_86), C_87)=k5_relat_1(A_85, k5_relat_1(B_86, C_87)) | ~v1_relat_1(C_87) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.45/4.90  tff(c_559, plain, (![A_31, B_32, C_87]: (k5_relat_1(k6_relat_1(A_31), k5_relat_1(B_32, C_87))=k5_relat_1(k7_relat_1(B_32, A_31), C_87) | ~v1_relat_1(C_87) | ~v1_relat_1(B_32) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_36, c_531])).
% 11.45/4.90  tff(c_1260, plain, (![A_126, B_127, C_128]: (k5_relat_1(k6_relat_1(A_126), k5_relat_1(B_127, C_128))=k5_relat_1(k7_relat_1(B_127, A_126), C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_559])).
% 11.45/4.90  tff(c_20395, plain, (![B_399, C_400, A_401]: (k7_relat_1(k5_relat_1(B_399, C_400), A_401)=k5_relat_1(k7_relat_1(B_399, A_401), C_400) | ~v1_relat_1(k5_relat_1(B_399, C_400)) | ~v1_relat_1(C_400) | ~v1_relat_1(B_399))), inference(superposition, [status(thm), theory('equality')], [c_1260, c_36])).
% 11.45/4.90  tff(c_20445, plain, (![A_26, A_401]: (k7_relat_1(k5_relat_1(k6_relat_1(A_26), k6_relat_1(A_26)), A_401)=k5_relat_1(k7_relat_1(k6_relat_1(A_26), A_401), k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_303, c_20395])).
% 11.45/4.90  tff(c_20510, plain, (![A_402, A_403]: (k5_relat_1(k7_relat_1(k6_relat_1(A_402), A_403), k6_relat_1(A_402))=k7_relat_1(k6_relat_1(A_402), A_403))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_18, c_303, c_20445])).
% 11.45/4.90  tff(c_266, plain, (![A_69, A_26]: (k5_relat_1(k6_relat_1(A_69), k6_relat_1(A_26))=k6_relat_1(A_26) | ~r1_tarski(A_26, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_260])).
% 11.45/4.90  tff(c_1294, plain, (![A_69, A_126, A_26]: (k5_relat_1(k7_relat_1(k6_relat_1(A_69), A_126), k6_relat_1(A_26))=k5_relat_1(k6_relat_1(A_126), k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_69)) | ~r1_tarski(A_26, A_69))), inference(superposition, [status(thm), theory('equality')], [c_266, c_1260])).
% 11.45/4.90  tff(c_1326, plain, (![A_69, A_126, A_26]: (k5_relat_1(k7_relat_1(k6_relat_1(A_69), A_126), k6_relat_1(A_26))=k5_relat_1(k6_relat_1(A_126), k6_relat_1(A_26)) | ~r1_tarski(A_26, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_1294])).
% 11.45/4.90  tff(c_20538, plain, (![A_403, A_402]: (k5_relat_1(k6_relat_1(A_403), k6_relat_1(A_402))=k7_relat_1(k6_relat_1(A_402), A_403) | ~r1_tarski(A_402, A_402))), inference(superposition, [status(thm), theory('equality')], [c_20510, c_1326])).
% 11.45/4.90  tff(c_20713, plain, (![A_403, A_402]: (k5_relat_1(k6_relat_1(A_403), k6_relat_1(A_402))=k7_relat_1(k6_relat_1(A_402), A_403))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20538])).
% 11.45/4.90  tff(c_453, plain, (![C_80, A_81, B_82]: (k7_relat_1(k7_relat_1(C_80, A_81), B_82)=k7_relat_1(C_80, k3_xboole_0(A_81, B_82)) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.45/4.90  tff(c_1608, plain, (![B_135, A_136, B_137]: (k7_relat_1(B_135, k3_xboole_0(k3_xboole_0(k1_relat_1(B_135), A_136), B_137))=k7_relat_1(k7_relat_1(B_135, A_136), B_137) | ~v1_relat_1(B_135) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_22, c_453])).
% 11.45/4.90  tff(c_10, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.45/4.90  tff(c_103, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.45/4.90  tff(c_118, plain, (![B_45, A_46]: (k1_setfam_1(k2_tarski(B_45, A_46))=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_10, c_103])).
% 11.45/4.90  tff(c_14, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.45/4.90  tff(c_124, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_118, c_14])).
% 11.45/4.90  tff(c_621, plain, (![B_45, A_46]: (k7_relat_1(k6_relat_1(B_45), k3_xboole_0(A_46, B_45))=k7_relat_1(k6_relat_1(B_45), A_46))), inference(superposition, [status(thm), theory('equality')], [c_124, c_591])).
% 11.45/4.90  tff(c_1626, plain, (![B_137, A_136]: (k7_relat_1(k6_relat_1(B_137), k3_xboole_0(k1_relat_1(k6_relat_1(B_137)), A_136))=k7_relat_1(k7_relat_1(k6_relat_1(B_137), A_136), B_137) | ~v1_relat_1(k6_relat_1(B_137)) | ~v1_relat_1(k6_relat_1(B_137)))), inference(superposition, [status(thm), theory('equality')], [c_1608, c_621])).
% 11.45/4.90  tff(c_1714, plain, (![B_137, A_136]: (k7_relat_1(k7_relat_1(k6_relat_1(B_137), A_136), B_137)=k7_relat_1(k6_relat_1(B_137), A_136))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_395, c_26, c_1626])).
% 11.45/4.90  tff(c_30, plain, (![A_27, B_28]: (r1_tarski(k5_relat_1(k6_relat_1(A_27), B_28), B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.45/4.90  tff(c_193, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.45/4.90  tff(c_918, plain, (![A_108, B_109]: (k5_relat_1(k6_relat_1(A_108), B_109)=B_109 | ~r1_tarski(B_109, k5_relat_1(k6_relat_1(A_108), B_109)) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_30, c_193])).
% 11.45/4.90  tff(c_9000, plain, (![A_256, B_257]: (k5_relat_1(k6_relat_1(A_256), B_257)=B_257 | ~r1_tarski(B_257, k7_relat_1(B_257, A_256)) | ~v1_relat_1(B_257) | ~v1_relat_1(B_257))), inference(superposition, [status(thm), theory('equality')], [c_36, c_918])).
% 11.45/4.90  tff(c_9018, plain, (![B_137, A_136]: (k5_relat_1(k6_relat_1(B_137), k7_relat_1(k6_relat_1(B_137), A_136))=k7_relat_1(k6_relat_1(B_137), A_136) | ~r1_tarski(k7_relat_1(k6_relat_1(B_137), A_136), k7_relat_1(k6_relat_1(B_137), A_136)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_137), A_136)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_137), A_136)))), inference(superposition, [status(thm), theory('equality')], [c_1714, c_9000])).
% 11.45/4.90  tff(c_9064, plain, (![B_137, A_136]: (k5_relat_1(k6_relat_1(B_137), k7_relat_1(k6_relat_1(B_137), A_136))=k7_relat_1(k6_relat_1(B_137), A_136))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_630, c_6, c_9018])).
% 11.45/4.90  tff(c_541, plain, (![A_85, B_86, A_27]: (r1_tarski(k5_relat_1(A_85, k5_relat_1(B_86, k6_relat_1(A_27))), k5_relat_1(A_85, B_86)) | ~v1_relat_1(k5_relat_1(A_85, B_86)) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_531, c_32])).
% 11.45/4.90  tff(c_2466, plain, (![A_154, B_155, A_156]: (r1_tarski(k5_relat_1(A_154, k5_relat_1(B_155, k6_relat_1(A_156))), k5_relat_1(A_154, B_155)) | ~v1_relat_1(k5_relat_1(A_154, B_155)) | ~v1_relat_1(B_155) | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_541])).
% 11.45/4.90  tff(c_2518, plain, (![A_154, A_156, A_31]: (r1_tarski(k5_relat_1(A_154, k7_relat_1(k6_relat_1(A_156), A_31)), k5_relat_1(A_154, k6_relat_1(A_31))) | ~v1_relat_1(k5_relat_1(A_154, k6_relat_1(A_31))) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(A_154) | ~v1_relat_1(k6_relat_1(A_156)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2466])).
% 11.45/4.90  tff(c_24991, plain, (![A_444, A_445, A_446]: (r1_tarski(k5_relat_1(A_444, k7_relat_1(k6_relat_1(A_445), A_446)), k5_relat_1(A_444, k6_relat_1(A_446))) | ~v1_relat_1(k5_relat_1(A_444, k6_relat_1(A_446))) | ~v1_relat_1(A_444))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_2518])).
% 11.45/4.90  tff(c_25004, plain, (![B_137, A_136]: (r1_tarski(k7_relat_1(k6_relat_1(B_137), A_136), k5_relat_1(k6_relat_1(B_137), k6_relat_1(A_136))) | ~v1_relat_1(k5_relat_1(k6_relat_1(B_137), k6_relat_1(A_136))) | ~v1_relat_1(k6_relat_1(B_137)))), inference(superposition, [status(thm), theory('equality')], [c_9064, c_24991])).
% 11.45/4.90  tff(c_25253, plain, (![B_447, A_448]: (r1_tarski(k7_relat_1(k6_relat_1(B_447), A_448), k7_relat_1(k6_relat_1(A_448), B_447)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_630, c_20713, c_20713, c_25004])).
% 11.45/4.90  tff(c_25459, plain, (![A_448, A_17]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_448)), A_17)), A_448), k7_relat_1(k6_relat_1(A_448), A_17)) | ~v1_relat_1(k6_relat_1(A_448)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_25253])).
% 11.45/4.90  tff(c_27293, plain, (![A_465, A_466]: (r1_tarski(k6_relat_1(k3_xboole_0(A_465, A_466)), k7_relat_1(k6_relat_1(A_465), A_466)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2324, c_26, c_25459])).
% 11.45/4.90  tff(c_27303, plain, (![A_465, A_466]: (k7_relat_1(k6_relat_1(A_465), A_466)=k6_relat_1(k3_xboole_0(A_465, A_466)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_465), A_466), k6_relat_1(k3_xboole_0(A_465, A_466))))), inference(resolution, [status(thm)], [c_27293, c_2])).
% 11.45/4.90  tff(c_27490, plain, (![A_465, A_466]: (k7_relat_1(k6_relat_1(A_465), A_466)=k6_relat_1(k3_xboole_0(A_465, A_466)))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_27303])).
% 11.45/4.90  tff(c_38, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.45/4.90  tff(c_229, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_38])).
% 11.45/4.90  tff(c_239, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_229])).
% 11.45/4.90  tff(c_27599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27490, c_239])).
% 11.45/4.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.45/4.90  
% 11.45/4.90  Inference rules
% 11.45/4.90  ----------------------
% 11.45/4.90  #Ref     : 0
% 11.45/4.90  #Sup     : 6665
% 11.45/4.90  #Fact    : 0
% 11.45/4.90  #Define  : 0
% 11.45/4.90  #Split   : 1
% 11.45/4.90  #Chain   : 0
% 11.45/4.90  #Close   : 0
% 11.45/4.90  
% 11.45/4.90  Ordering : KBO
% 11.45/4.90  
% 11.45/4.90  Simplification rules
% 11.45/4.90  ----------------------
% 11.45/4.90  #Subsume      : 916
% 11.45/4.90  #Demod        : 7428
% 11.45/4.90  #Tautology    : 2331
% 11.45/4.90  #SimpNegUnit  : 0
% 11.45/4.90  #BackRed      : 62
% 11.45/4.90  
% 11.45/4.90  #Partial instantiations: 0
% 11.45/4.90  #Strategies tried      : 1
% 11.45/4.90  
% 11.45/4.90  Timing (in seconds)
% 11.45/4.90  ----------------------
% 11.45/4.91  Preprocessing        : 0.36
% 11.45/4.91  Parsing              : 0.19
% 11.45/4.91  CNF conversion       : 0.02
% 11.45/4.91  Main loop            : 3.71
% 11.45/4.91  Inferencing          : 0.80
% 11.45/4.91  Reduction            : 1.80
% 11.45/4.91  Demodulation         : 1.56
% 11.45/4.91  BG Simplification    : 0.12
% 11.45/4.91  Subsumption          : 0.80
% 11.45/4.91  Abstraction          : 0.18
% 11.45/4.91  MUC search           : 0.00
% 11.45/4.91  Cooper               : 0.00
% 11.45/4.91  Total                : 4.12
% 11.45/4.91  Index Insertion      : 0.00
% 11.45/4.91  Index Deletion       : 0.00
% 11.45/4.91  Index Matching       : 0.00
% 11.45/4.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
