%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:25 EST 2020

% Result     : Theorem 15.81s
% Output     : CNFRefutation 15.98s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 315 expanded)
%              Number of leaves         :   32 ( 125 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 ( 519 expanded)
%              Number of equality atoms :   49 ( 200 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_46,plain,(
    ! [A_40] : v1_relat_1(k6_relat_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_31] : k1_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_593,plain,(
    ! [B_91,A_92] :
      ( k7_relat_1(B_91,k3_xboole_0(k1_relat_1(B_91),A_92)) = k7_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_390,plain,(
    ! [A_80,B_81] :
      ( k5_relat_1(k6_relat_1(A_80),B_81) = k7_relat_1(B_81,A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k5_relat_1(B_33,k6_relat_1(A_32)),B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_401,plain,(
    ! [A_32,A_80] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_32),A_80),k6_relat_1(A_80))
      | ~ v1_relat_1(k6_relat_1(A_80))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_36])).

tff(c_431,plain,(
    ! [A_32,A_80] : r1_tarski(k7_relat_1(k6_relat_1(A_32),A_80),k6_relat_1(A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_401])).

tff(c_600,plain,(
    ! [A_32,A_92] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_32),A_92),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_32)),A_92)))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_431])).

tff(c_625,plain,(
    ! [A_32,A_92] : r1_tarski(k7_relat_1(k6_relat_1(A_32),A_92),k6_relat_1(k3_xboole_0(A_32,A_92))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_30,c_600])).

tff(c_32,plain,(
    ! [A_31] : k2_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    ! [A_37] :
      ( k5_relat_1(A_37,k6_relat_1(k2_relat_1(A_37))) = A_37
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_409,plain,(
    ! [A_80] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80))),A_80) = k6_relat_1(A_80)
      | ~ v1_relat_1(k6_relat_1(A_80))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_42])).

tff(c_435,plain,(
    ! [A_80] : k7_relat_1(k6_relat_1(A_80),A_80) = k6_relat_1(A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_32,c_409])).

tff(c_622,plain,(
    ! [A_31,A_92] :
      ( k7_relat_1(k6_relat_1(A_31),k3_xboole_0(A_31,A_92)) = k7_relat_1(k6_relat_1(A_31),A_92)
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_593])).

tff(c_630,plain,(
    ! [A_31,A_92] : k7_relat_1(k6_relat_1(A_31),k3_xboole_0(A_31,A_92)) = k7_relat_1(k6_relat_1(A_31),A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_622])).

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_142,plain,(
    ! [A_57,B_58] : k1_setfam_1(k2_tarski(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    ! [B_59,A_60] : k1_setfam_1(k2_tarski(B_59,A_60)) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_142])).

tff(c_20,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [B_59,A_60] : k3_xboole_0(B_59,A_60) = k3_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_20])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_32),B_33),B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1185,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(k7_relat_1(B_112,A_113),B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_34])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1190,plain,(
    ! [B_112,A_113] :
      ( k3_xboole_0(k7_relat_1(B_112,A_113),B_112) = k7_relat_1(B_112,A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_1185,c_10])).

tff(c_4023,plain,(
    ! [B_182,A_183] :
      ( k3_xboole_0(B_182,k7_relat_1(B_182,A_183)) = k7_relat_1(B_182,A_183)
      | ~ v1_relat_1(B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1190])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4232,plain,(
    ! [B_186,A_187] :
      ( v1_relat_1(k7_relat_1(B_186,A_187))
      | ~ v1_relat_1(B_186)
      | ~ v1_relat_1(B_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4023,c_22])).

tff(c_4241,plain,(
    ! [A_31,A_92] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_31),A_92))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_4232])).

tff(c_4259,plain,(
    ! [A_31,A_92] : v1_relat_1(k7_relat_1(k6_relat_1(A_31),A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_4241])).

tff(c_4140,plain,(
    ! [A_31,A_92] :
      ( k3_xboole_0(k6_relat_1(A_31),k7_relat_1(k6_relat_1(A_31),A_92)) = k7_relat_1(k6_relat_1(A_31),k3_xboole_0(A_31,A_92))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_4023])).

tff(c_30566,plain,(
    ! [A_478,A_479] : k3_xboole_0(k6_relat_1(A_478),k7_relat_1(k6_relat_1(A_478),A_479)) = k7_relat_1(k6_relat_1(A_478),A_479) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_630,c_4140])).

tff(c_44,plain,(
    ! [A_38,B_39] :
      ( k5_relat_1(k6_relat_1(A_38),B_39) = k7_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_225,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_63),B_64),B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_228,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(k5_relat_1(k6_relat_1(A_63),B_64),B_64) = k5_relat_1(k6_relat_1(A_63),B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_225,c_10])).

tff(c_15671,plain,(
    ! [B_336,A_337] :
      ( k3_xboole_0(B_336,k5_relat_1(k6_relat_1(A_337),B_336)) = k5_relat_1(k6_relat_1(A_337),B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_228])).

tff(c_15934,plain,(
    ! [A_38,B_39] :
      ( k5_relat_1(k6_relat_1(A_38),B_39) = k3_xboole_0(B_39,k7_relat_1(B_39,A_38))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_15671])).

tff(c_30590,plain,(
    ! [A_479,A_478] :
      ( k5_relat_1(k6_relat_1(A_479),k6_relat_1(A_478)) = k7_relat_1(k6_relat_1(A_478),A_479)
      | ~ v1_relat_1(k6_relat_1(A_478))
      | ~ v1_relat_1(k6_relat_1(A_478)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30566,c_15934])).

tff(c_30992,plain,(
    ! [A_479,A_478] : k5_relat_1(k6_relat_1(A_479),k6_relat_1(A_478)) = k7_relat_1(k6_relat_1(A_478),A_479) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_30590])).

tff(c_915,plain,(
    ! [C_101,A_102,B_103] :
      ( k7_relat_1(k7_relat_1(C_101,A_102),B_103) = k7_relat_1(C_101,k3_xboole_0(A_102,B_103))
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( k7_relat_1(k7_relat_1(C_21,A_19),B_20) = k7_relat_1(C_21,k3_xboole_0(A_19,B_20))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7549,plain,(
    ! [C_252,A_253,B_254,B_255] :
      ( k7_relat_1(k7_relat_1(C_252,k3_xboole_0(A_253,B_254)),B_255) = k7_relat_1(k7_relat_1(C_252,A_253),k3_xboole_0(B_254,B_255))
      | ~ v1_relat_1(k7_relat_1(C_252,A_253))
      | ~ v1_relat_1(C_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_24])).

tff(c_7669,plain,(
    ! [A_31,A_92,B_255] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_31),A_31),k3_xboole_0(A_92,B_255)) = k7_relat_1(k7_relat_1(k6_relat_1(A_31),A_92),B_255)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_31),A_31))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_7549])).

tff(c_7739,plain,(
    ! [A_31,A_92,B_255] : k7_relat_1(k7_relat_1(k6_relat_1(A_31),A_92),B_255) = k7_relat_1(k6_relat_1(A_31),k3_xboole_0(A_92,B_255)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_435,c_435,c_7669])).

tff(c_949,plain,(
    ! [A_104,B_105,C_106] :
      ( k5_relat_1(k5_relat_1(A_104,B_105),C_106) = k5_relat_1(A_104,k5_relat_1(B_105,C_106))
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_959,plain,(
    ! [A_104,B_105,A_32] :
      ( r1_tarski(k5_relat_1(A_104,k5_relat_1(B_105,k6_relat_1(A_32))),k5_relat_1(A_104,B_105))
      | ~ v1_relat_1(k5_relat_1(A_104,B_105))
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(B_105)
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_36])).

tff(c_6782,plain,(
    ! [A_235,B_236,A_237] :
      ( r1_tarski(k5_relat_1(A_235,k5_relat_1(B_236,k6_relat_1(A_237))),k5_relat_1(A_235,B_236))
      | ~ v1_relat_1(k5_relat_1(A_235,B_236))
      | ~ v1_relat_1(B_236)
      | ~ v1_relat_1(A_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_959])).

tff(c_6840,plain,(
    ! [A_235,A_237,A_38] :
      ( r1_tarski(k5_relat_1(A_235,k7_relat_1(k6_relat_1(A_237),A_38)),k5_relat_1(A_235,k6_relat_1(A_38)))
      | ~ v1_relat_1(k5_relat_1(A_235,k6_relat_1(A_38)))
      | ~ v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(A_235)
      | ~ v1_relat_1(k6_relat_1(A_237)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_6782])).

tff(c_48337,plain,(
    ! [A_600,A_601,A_602] :
      ( r1_tarski(k5_relat_1(A_600,k7_relat_1(k6_relat_1(A_601),A_602)),k5_relat_1(A_600,k6_relat_1(A_602)))
      | ~ v1_relat_1(k5_relat_1(A_600,k6_relat_1(A_602)))
      | ~ v1_relat_1(A_600) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_6840])).

tff(c_48531,plain,(
    ! [A_601,A_602,A_38] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_601),A_602),A_38),k5_relat_1(k6_relat_1(A_38),k6_relat_1(A_602)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_38),k6_relat_1(A_602)))
      | ~ v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_601),A_602)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_48337])).

tff(c_48622,plain,(
    ! [A_603,A_604,A_605] : r1_tarski(k7_relat_1(k6_relat_1(A_603),k3_xboole_0(A_604,A_605)),k7_relat_1(k6_relat_1(A_604),A_605)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4259,c_46,c_4259,c_30992,c_30992,c_7739,c_48531])).

tff(c_50791,plain,(
    ! [A_612,A_613] : r1_tarski(k6_relat_1(k3_xboole_0(A_612,A_613)),k7_relat_1(k6_relat_1(A_612),A_613)) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_48622])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50798,plain,(
    ! [A_612,A_613] :
      ( k7_relat_1(k6_relat_1(A_612),A_613) = k6_relat_1(k3_xboole_0(A_612,A_613))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_612),A_613),k6_relat_1(k3_xboole_0(A_612,A_613))) ) ),
    inference(resolution,[status(thm)],[c_50791,c_2])).

tff(c_51023,plain,(
    ! [A_612,A_613] : k7_relat_1(k6_relat_1(A_612),A_613) = k6_relat_1(k3_xboole_0(A_612,A_613)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_50798])).

tff(c_50,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_415,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_50])).

tff(c_437,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_415])).

tff(c_51163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51023,c_437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:33:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.81/8.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.81/8.66  
% 15.81/8.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.92/8.66  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 15.92/8.66  
% 15.92/8.66  %Foreground sorts:
% 15.92/8.66  
% 15.92/8.66  
% 15.92/8.66  %Background operators:
% 15.92/8.66  
% 15.92/8.66  
% 15.92/8.66  %Foreground operators:
% 15.92/8.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.92/8.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.92/8.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.92/8.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.92/8.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.92/8.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.92/8.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.92/8.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.92/8.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.92/8.66  tff('#skF_2', type, '#skF_2': $i).
% 15.92/8.66  tff('#skF_1', type, '#skF_1': $i).
% 15.92/8.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.92/8.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.92/8.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.92/8.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.92/8.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.92/8.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.92/8.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.92/8.66  
% 15.98/8.68  tff(f_101, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 15.98/8.68  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 15.98/8.68  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 15.98/8.68  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 15.98/8.68  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 15.98/8.68  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 15.98/8.68  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 15.98/8.68  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 15.98/8.68  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.98/8.68  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 15.98/8.68  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 15.98/8.68  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 15.98/8.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.98/8.68  tff(f_104, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 15.98/8.68  tff(c_46, plain, (![A_40]: (v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.98/8.68  tff(c_30, plain, (![A_31]: (k1_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.98/8.68  tff(c_593, plain, (![B_91, A_92]: (k7_relat_1(B_91, k3_xboole_0(k1_relat_1(B_91), A_92))=k7_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.98/8.68  tff(c_390, plain, (![A_80, B_81]: (k5_relat_1(k6_relat_1(A_80), B_81)=k7_relat_1(B_81, A_80) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_97])).
% 15.98/8.68  tff(c_36, plain, (![B_33, A_32]: (r1_tarski(k5_relat_1(B_33, k6_relat_1(A_32)), B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.98/8.68  tff(c_401, plain, (![A_32, A_80]: (r1_tarski(k7_relat_1(k6_relat_1(A_32), A_80), k6_relat_1(A_80)) | ~v1_relat_1(k6_relat_1(A_80)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_390, c_36])).
% 15.98/8.68  tff(c_431, plain, (![A_32, A_80]: (r1_tarski(k7_relat_1(k6_relat_1(A_32), A_80), k6_relat_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_401])).
% 15.98/8.68  tff(c_600, plain, (![A_32, A_92]: (r1_tarski(k7_relat_1(k6_relat_1(A_32), A_92), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_32)), A_92))) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_593, c_431])).
% 15.98/8.68  tff(c_625, plain, (![A_32, A_92]: (r1_tarski(k7_relat_1(k6_relat_1(A_32), A_92), k6_relat_1(k3_xboole_0(A_32, A_92))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_30, c_600])).
% 15.98/8.68  tff(c_32, plain, (![A_31]: (k2_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.98/8.68  tff(c_42, plain, (![A_37]: (k5_relat_1(A_37, k6_relat_1(k2_relat_1(A_37)))=A_37 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_93])).
% 15.98/8.68  tff(c_409, plain, (![A_80]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80))), A_80)=k6_relat_1(A_80) | ~v1_relat_1(k6_relat_1(A_80)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_80)))))), inference(superposition, [status(thm), theory('equality')], [c_390, c_42])).
% 15.98/8.68  tff(c_435, plain, (![A_80]: (k7_relat_1(k6_relat_1(A_80), A_80)=k6_relat_1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_32, c_409])).
% 15.98/8.68  tff(c_622, plain, (![A_31, A_92]: (k7_relat_1(k6_relat_1(A_31), k3_xboole_0(A_31, A_92))=k7_relat_1(k6_relat_1(A_31), A_92) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_593])).
% 15.98/8.68  tff(c_630, plain, (![A_31, A_92]: (k7_relat_1(k6_relat_1(A_31), k3_xboole_0(A_31, A_92))=k7_relat_1(k6_relat_1(A_31), A_92))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_622])).
% 15.98/8.68  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.98/8.68  tff(c_142, plain, (![A_57, B_58]: (k1_setfam_1(k2_tarski(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.98/8.68  tff(c_157, plain, (![B_59, A_60]: (k1_setfam_1(k2_tarski(B_59, A_60))=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_16, c_142])).
% 15.98/8.68  tff(c_20, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.98/8.68  tff(c_163, plain, (![B_59, A_60]: (k3_xboole_0(B_59, A_60)=k3_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_157, c_20])).
% 15.98/8.68  tff(c_34, plain, (![A_32, B_33]: (r1_tarski(k5_relat_1(k6_relat_1(A_32), B_33), B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.98/8.68  tff(c_1185, plain, (![B_112, A_113]: (r1_tarski(k7_relat_1(B_112, A_113), B_112) | ~v1_relat_1(B_112) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_390, c_34])).
% 15.98/8.68  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.98/8.68  tff(c_1190, plain, (![B_112, A_113]: (k3_xboole_0(k7_relat_1(B_112, A_113), B_112)=k7_relat_1(B_112, A_113) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_1185, c_10])).
% 15.98/8.68  tff(c_4023, plain, (![B_182, A_183]: (k3_xboole_0(B_182, k7_relat_1(B_182, A_183))=k7_relat_1(B_182, A_183) | ~v1_relat_1(B_182))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1190])).
% 15.98/8.68  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k3_xboole_0(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.98/8.68  tff(c_4232, plain, (![B_186, A_187]: (v1_relat_1(k7_relat_1(B_186, A_187)) | ~v1_relat_1(B_186) | ~v1_relat_1(B_186))), inference(superposition, [status(thm), theory('equality')], [c_4023, c_22])).
% 15.98/8.68  tff(c_4241, plain, (![A_31, A_92]: (v1_relat_1(k7_relat_1(k6_relat_1(A_31), A_92)) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_630, c_4232])).
% 15.98/8.68  tff(c_4259, plain, (![A_31, A_92]: (v1_relat_1(k7_relat_1(k6_relat_1(A_31), A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_4241])).
% 15.98/8.68  tff(c_4140, plain, (![A_31, A_92]: (k3_xboole_0(k6_relat_1(A_31), k7_relat_1(k6_relat_1(A_31), A_92))=k7_relat_1(k6_relat_1(A_31), k3_xboole_0(A_31, A_92)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_630, c_4023])).
% 15.98/8.68  tff(c_30566, plain, (![A_478, A_479]: (k3_xboole_0(k6_relat_1(A_478), k7_relat_1(k6_relat_1(A_478), A_479))=k7_relat_1(k6_relat_1(A_478), A_479))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_630, c_4140])).
% 15.98/8.68  tff(c_44, plain, (![A_38, B_39]: (k5_relat_1(k6_relat_1(A_38), B_39)=k7_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_97])).
% 15.98/8.68  tff(c_225, plain, (![A_63, B_64]: (r1_tarski(k5_relat_1(k6_relat_1(A_63), B_64), B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.98/8.68  tff(c_228, plain, (![A_63, B_64]: (k3_xboole_0(k5_relat_1(k6_relat_1(A_63), B_64), B_64)=k5_relat_1(k6_relat_1(A_63), B_64) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_225, c_10])).
% 15.98/8.68  tff(c_15671, plain, (![B_336, A_337]: (k3_xboole_0(B_336, k5_relat_1(k6_relat_1(A_337), B_336))=k5_relat_1(k6_relat_1(A_337), B_336) | ~v1_relat_1(B_336))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_228])).
% 15.98/8.68  tff(c_15934, plain, (![A_38, B_39]: (k5_relat_1(k6_relat_1(A_38), B_39)=k3_xboole_0(B_39, k7_relat_1(B_39, A_38)) | ~v1_relat_1(B_39) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_44, c_15671])).
% 15.98/8.68  tff(c_30590, plain, (![A_479, A_478]: (k5_relat_1(k6_relat_1(A_479), k6_relat_1(A_478))=k7_relat_1(k6_relat_1(A_478), A_479) | ~v1_relat_1(k6_relat_1(A_478)) | ~v1_relat_1(k6_relat_1(A_478)))), inference(superposition, [status(thm), theory('equality')], [c_30566, c_15934])).
% 15.98/8.68  tff(c_30992, plain, (![A_479, A_478]: (k5_relat_1(k6_relat_1(A_479), k6_relat_1(A_478))=k7_relat_1(k6_relat_1(A_478), A_479))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_30590])).
% 15.98/8.68  tff(c_915, plain, (![C_101, A_102, B_103]: (k7_relat_1(k7_relat_1(C_101, A_102), B_103)=k7_relat_1(C_101, k3_xboole_0(A_102, B_103)) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.98/8.68  tff(c_24, plain, (![C_21, A_19, B_20]: (k7_relat_1(k7_relat_1(C_21, A_19), B_20)=k7_relat_1(C_21, k3_xboole_0(A_19, B_20)) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.98/8.68  tff(c_7549, plain, (![C_252, A_253, B_254, B_255]: (k7_relat_1(k7_relat_1(C_252, k3_xboole_0(A_253, B_254)), B_255)=k7_relat_1(k7_relat_1(C_252, A_253), k3_xboole_0(B_254, B_255)) | ~v1_relat_1(k7_relat_1(C_252, A_253)) | ~v1_relat_1(C_252))), inference(superposition, [status(thm), theory('equality')], [c_915, c_24])).
% 15.98/8.68  tff(c_7669, plain, (![A_31, A_92, B_255]: (k7_relat_1(k7_relat_1(k6_relat_1(A_31), A_31), k3_xboole_0(A_92, B_255))=k7_relat_1(k7_relat_1(k6_relat_1(A_31), A_92), B_255) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_31), A_31)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_630, c_7549])).
% 15.98/8.68  tff(c_7739, plain, (![A_31, A_92, B_255]: (k7_relat_1(k7_relat_1(k6_relat_1(A_31), A_92), B_255)=k7_relat_1(k6_relat_1(A_31), k3_xboole_0(A_92, B_255)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_435, c_435, c_7669])).
% 15.98/8.68  tff(c_949, plain, (![A_104, B_105, C_106]: (k5_relat_1(k5_relat_1(A_104, B_105), C_106)=k5_relat_1(A_104, k5_relat_1(B_105, C_106)) | ~v1_relat_1(C_106) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.98/8.68  tff(c_959, plain, (![A_104, B_105, A_32]: (r1_tarski(k5_relat_1(A_104, k5_relat_1(B_105, k6_relat_1(A_32))), k5_relat_1(A_104, B_105)) | ~v1_relat_1(k5_relat_1(A_104, B_105)) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(B_105) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_949, c_36])).
% 15.98/8.68  tff(c_6782, plain, (![A_235, B_236, A_237]: (r1_tarski(k5_relat_1(A_235, k5_relat_1(B_236, k6_relat_1(A_237))), k5_relat_1(A_235, B_236)) | ~v1_relat_1(k5_relat_1(A_235, B_236)) | ~v1_relat_1(B_236) | ~v1_relat_1(A_235))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_959])).
% 15.98/8.68  tff(c_6840, plain, (![A_235, A_237, A_38]: (r1_tarski(k5_relat_1(A_235, k7_relat_1(k6_relat_1(A_237), A_38)), k5_relat_1(A_235, k6_relat_1(A_38))) | ~v1_relat_1(k5_relat_1(A_235, k6_relat_1(A_38))) | ~v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(A_235) | ~v1_relat_1(k6_relat_1(A_237)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_6782])).
% 15.98/8.68  tff(c_48337, plain, (![A_600, A_601, A_602]: (r1_tarski(k5_relat_1(A_600, k7_relat_1(k6_relat_1(A_601), A_602)), k5_relat_1(A_600, k6_relat_1(A_602))) | ~v1_relat_1(k5_relat_1(A_600, k6_relat_1(A_602))) | ~v1_relat_1(A_600))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_6840])).
% 15.98/8.68  tff(c_48531, plain, (![A_601, A_602, A_38]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_601), A_602), A_38), k5_relat_1(k6_relat_1(A_38), k6_relat_1(A_602))) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_38), k6_relat_1(A_602))) | ~v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_601), A_602)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_48337])).
% 15.98/8.68  tff(c_48622, plain, (![A_603, A_604, A_605]: (r1_tarski(k7_relat_1(k6_relat_1(A_603), k3_xboole_0(A_604, A_605)), k7_relat_1(k6_relat_1(A_604), A_605)))), inference(demodulation, [status(thm), theory('equality')], [c_4259, c_46, c_4259, c_30992, c_30992, c_7739, c_48531])).
% 15.98/8.68  tff(c_50791, plain, (![A_612, A_613]: (r1_tarski(k6_relat_1(k3_xboole_0(A_612, A_613)), k7_relat_1(k6_relat_1(A_612), A_613)))), inference(superposition, [status(thm), theory('equality')], [c_435, c_48622])).
% 15.98/8.68  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.98/8.68  tff(c_50798, plain, (![A_612, A_613]: (k7_relat_1(k6_relat_1(A_612), A_613)=k6_relat_1(k3_xboole_0(A_612, A_613)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_612), A_613), k6_relat_1(k3_xboole_0(A_612, A_613))))), inference(resolution, [status(thm)], [c_50791, c_2])).
% 15.98/8.68  tff(c_51023, plain, (![A_612, A_613]: (k7_relat_1(k6_relat_1(A_612), A_613)=k6_relat_1(k3_xboole_0(A_612, A_613)))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_50798])).
% 15.98/8.68  tff(c_50, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.98/8.68  tff(c_415, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_390, c_50])).
% 15.98/8.68  tff(c_437, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_415])).
% 15.98/8.68  tff(c_51163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51023, c_437])).
% 15.98/8.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.98/8.68  
% 15.98/8.68  Inference rules
% 15.98/8.68  ----------------------
% 15.98/8.68  #Ref     : 0
% 15.98/8.68  #Sup     : 12747
% 15.98/8.68  #Fact    : 0
% 15.98/8.68  #Define  : 0
% 15.98/8.68  #Split   : 1
% 15.98/8.68  #Chain   : 0
% 15.98/8.68  #Close   : 0
% 15.98/8.68  
% 15.98/8.68  Ordering : KBO
% 15.98/8.68  
% 15.98/8.68  Simplification rules
% 15.98/8.68  ----------------------
% 15.98/8.68  #Subsume      : 1264
% 15.98/8.68  #Demod        : 15916
% 15.98/8.68  #Tautology    : 5507
% 15.98/8.68  #SimpNegUnit  : 0
% 15.98/8.68  #BackRed      : 89
% 15.98/8.68  
% 15.98/8.68  #Partial instantiations: 0
% 15.98/8.68  #Strategies tried      : 1
% 15.98/8.68  
% 15.98/8.68  Timing (in seconds)
% 15.98/8.68  ----------------------
% 15.98/8.68  Preprocessing        : 0.33
% 15.98/8.68  Parsing              : 0.17
% 15.98/8.68  CNF conversion       : 0.02
% 15.98/8.68  Main loop            : 7.59
% 15.98/8.69  Inferencing          : 1.20
% 15.98/8.69  Reduction            : 4.42
% 15.98/8.69  Demodulation         : 4.00
% 15.98/8.69  BG Simplification    : 0.17
% 15.98/8.69  Subsumption          : 1.46
% 15.98/8.69  Abstraction          : 0.32
% 15.98/8.69  MUC search           : 0.00
% 15.98/8.69  Cooper               : 0.00
% 15.98/8.69  Total                : 7.95
% 15.98/8.69  Index Insertion      : 0.00
% 15.98/8.69  Index Deletion       : 0.00
% 15.98/8.69  Index Matching       : 0.00
% 15.98/8.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
