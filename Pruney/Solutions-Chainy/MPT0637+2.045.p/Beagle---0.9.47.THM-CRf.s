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
% DateTime   : Thu Dec  3 10:03:30 EST 2020

% Result     : Theorem 16.25s
% Output     : CNFRefutation 16.34s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 926 expanded)
%              Number of leaves         :   37 ( 344 expanded)
%              Depth                    :   18
%              Number of atoms          :  175 (1667 expanded)
%              Number of equality atoms :   49 ( 441 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_59,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_26,plain,(
    ! [A_37] : v1_relat_1(k6_relat_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_63] : k1_relat_1(k6_relat_1(A_63)) = A_63 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_494,plain,(
    ! [B_129,A_130] :
      ( k3_xboole_0(k1_relat_1(B_129),A_130) = k1_relat_1(k7_relat_1(B_129,A_130))
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_503,plain,(
    ! [A_63,A_130] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_63),A_130)) = k3_xboole_0(A_63,A_130)
      | ~ v1_relat_1(k6_relat_1(A_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_494])).

tff(c_507,plain,(
    ! [A_63,A_130] : k1_relat_1(k7_relat_1(k6_relat_1(A_63),A_130)) = k3_xboole_0(A_63,A_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_503])).

tff(c_181,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_96,A_97)),k1_relat_1(B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_188,plain,(
    ! [A_63,A_97] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_63),A_97)),A_63)
      | ~ v1_relat_1(k6_relat_1(A_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_181])).

tff(c_192,plain,(
    ! [A_63,A_97] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_63),A_97)),A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_188])).

tff(c_508,plain,(
    ! [A_63,A_97] : r1_tarski(k3_xboole_0(A_63,A_97),A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_192])).

tff(c_30,plain,(
    ! [B_43,A_42] :
      ( k5_relat_1(B_43,k6_relat_1(A_42)) = k8_relat_1(A_42,B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_273,plain,(
    ! [A_107,B_108] :
      ( k5_relat_1(k6_relat_1(A_107),B_108) = k7_relat_1(B_108,A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_308,plain,(
    ! [A_42,A_107] :
      ( k8_relat_1(A_42,k6_relat_1(A_107)) = k7_relat_1(k6_relat_1(A_42),A_107)
      | ~ v1_relat_1(k6_relat_1(A_42))
      | ~ v1_relat_1(k6_relat_1(A_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_273])).

tff(c_402,plain,(
    ! [A_117,A_118] : k8_relat_1(A_117,k6_relat_1(A_118)) = k7_relat_1(k6_relat_1(A_117),A_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_308])).

tff(c_193,plain,(
    ! [B_98,A_99] :
      ( k5_relat_1(B_98,k6_relat_1(A_99)) = k8_relat_1(A_99,B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [A_35,B_36] :
      ( v1_relat_1(k5_relat_1(A_35,B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_214,plain,(
    ! [A_99,B_98] :
      ( v1_relat_1(k8_relat_1(A_99,B_98))
      | ~ v1_relat_1(k6_relat_1(A_99))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_24])).

tff(c_235,plain,(
    ! [A_99,B_98] :
      ( v1_relat_1(k8_relat_1(A_99,B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_214])).

tff(c_412,plain,(
    ! [A_117,A_118] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_117),A_118))
      | ~ v1_relat_1(k6_relat_1(A_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_235])).

tff(c_422,plain,(
    ! [A_117,A_118] : v1_relat_1(k7_relat_1(k6_relat_1(A_117),A_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_412])).

tff(c_331,plain,(
    ! [A_42,A_107] : k8_relat_1(A_42,k6_relat_1(A_107)) = k7_relat_1(k6_relat_1(A_42),A_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_308])).

tff(c_1807,plain,(
    ! [A_212,B_213,C_214] :
      ( k8_relat_1(A_212,k5_relat_1(B_213,C_214)) = k5_relat_1(B_213,k8_relat_1(A_212,C_214))
      | ~ v1_relat_1(C_214)
      | ~ v1_relat_1(B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1842,plain,(
    ! [B_43,A_212,A_42] :
      ( k5_relat_1(B_43,k8_relat_1(A_212,k6_relat_1(A_42))) = k8_relat_1(A_212,k8_relat_1(A_42,B_43))
      | ~ v1_relat_1(k6_relat_1(A_42))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1807])).

tff(c_1858,plain,(
    ! [B_43,A_212,A_42] :
      ( k5_relat_1(B_43,k7_relat_1(k6_relat_1(A_212),A_42)) = k8_relat_1(A_212,k8_relat_1(A_42,B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_331,c_1842])).

tff(c_48,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_64),B_65),B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_200,plain,(
    ! [A_99,A_64] :
      ( r1_tarski(k8_relat_1(A_99,k6_relat_1(A_64)),k6_relat_1(A_99))
      | ~ v1_relat_1(k6_relat_1(A_99))
      | ~ v1_relat_1(k6_relat_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_48])).

tff(c_229,plain,(
    ! [A_99,A_64] : r1_tarski(k8_relat_1(A_99,k6_relat_1(A_64)),k6_relat_1(A_99)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_200])).

tff(c_400,plain,(
    ! [A_99,A_64] : r1_tarski(k7_relat_1(k6_relat_1(A_99),A_64),k6_relat_1(A_99)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_229])).

tff(c_988,plain,(
    ! [A_167,B_168] :
      ( r1_tarski(k1_relat_1(A_167),k1_relat_1(B_168))
      | ~ r1_tarski(A_167,B_168)
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1007,plain,(
    ! [A_167,A_63] :
      ( r1_tarski(k1_relat_1(A_167),A_63)
      | ~ r1_tarski(A_167,k6_relat_1(A_63))
      | ~ v1_relat_1(k6_relat_1(A_63))
      | ~ v1_relat_1(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_988])).

tff(c_1863,plain,(
    ! [A_215,A_216] :
      ( r1_tarski(k1_relat_1(A_215),A_216)
      | ~ r1_tarski(A_215,k6_relat_1(A_216))
      | ~ v1_relat_1(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1007])).

tff(c_52,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_relat_1(A_66),B_67) = B_67
      | ~ r1_tarski(k1_relat_1(B_67),A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4329,plain,(
    ! [A_327,A_328] :
      ( k5_relat_1(k6_relat_1(A_327),A_328) = A_328
      | ~ r1_tarski(A_328,k6_relat_1(A_327))
      | ~ v1_relat_1(A_328) ) ),
    inference(resolution,[status(thm)],[c_1863,c_52])).

tff(c_4457,plain,(
    ! [A_99,A_64] :
      ( k5_relat_1(k6_relat_1(A_99),k7_relat_1(k6_relat_1(A_99),A_64)) = k7_relat_1(k6_relat_1(A_99),A_64)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_99),A_64)) ) ),
    inference(resolution,[status(thm)],[c_400,c_4329])).

tff(c_9463,plain,(
    ! [A_467,A_468] : k5_relat_1(k6_relat_1(A_467),k7_relat_1(k6_relat_1(A_467),A_468)) = k7_relat_1(k6_relat_1(A_467),A_468) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_4457])).

tff(c_9532,plain,(
    ! [A_212,A_42] :
      ( k8_relat_1(A_212,k8_relat_1(A_42,k6_relat_1(A_212))) = k7_relat_1(k6_relat_1(A_212),A_42)
      | ~ v1_relat_1(k6_relat_1(A_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1858,c_9463])).

tff(c_10056,plain,(
    ! [A_485,A_486] : k8_relat_1(A_485,k7_relat_1(k6_relat_1(A_486),A_485)) = k7_relat_1(k6_relat_1(A_485),A_486) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_331,c_9532])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [B_65,A_64] :
      ( r1_tarski(k5_relat_1(B_65,k6_relat_1(A_64)),B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_827,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(k8_relat_1(A_156,B_157),B_157)
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_50])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1974,plain,(
    ! [A_229,B_230,A_231] :
      ( r1_tarski(A_229,B_230)
      | ~ r1_tarski(A_229,k8_relat_1(A_231,B_230))
      | ~ v1_relat_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_827,c_8])).

tff(c_2080,plain,(
    ! [A_231,B_230] :
      ( r1_tarski(k8_relat_1(A_231,B_230),B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_6,c_1974])).

tff(c_10108,plain,(
    ! [A_485,A_486] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_485),A_486),k7_relat_1(k6_relat_1(A_486),A_485))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_486),A_485)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10056,c_2080])).

tff(c_10161,plain,(
    ! [A_485,A_486] : r1_tarski(k7_relat_1(k6_relat_1(A_485),A_486),k7_relat_1(k6_relat_1(A_486),A_485)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_10108])).

tff(c_10174,plain,(
    ! [A_487,A_488] : r1_tarski(k7_relat_1(k6_relat_1(A_487),A_488),k7_relat_1(k6_relat_1(A_488),A_487)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_10108])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10190,plain,(
    ! [A_488,A_487] :
      ( k7_relat_1(k6_relat_1(A_488),A_487) = k7_relat_1(k6_relat_1(A_487),A_488)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_488),A_487),k7_relat_1(k6_relat_1(A_487),A_488)) ) ),
    inference(resolution,[status(thm)],[c_10174,c_2])).

tff(c_10230,plain,(
    ! [A_490,A_489] : k7_relat_1(k6_relat_1(A_490),A_489) = k7_relat_1(k6_relat_1(A_489),A_490) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10161,c_10190])).

tff(c_56,plain,(
    ! [B_70,A_69] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_70,A_69)),k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_10633,plain,(
    ! [A_490,A_489] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_490),A_489)),k1_relat_1(k6_relat_1(A_489)))
      | ~ v1_relat_1(k6_relat_1(A_489)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10230,c_56])).

tff(c_10758,plain,(
    ! [A_490,A_489] : r1_tarski(k3_xboole_0(A_490,A_489),A_489) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_507,c_44,c_10633])).

tff(c_602,plain,(
    ! [A_139,B_140] :
      ( k5_relat_1(k6_relat_1(A_139),B_140) = B_140
      | ~ r1_tarski(k1_relat_1(B_140),A_139)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_611,plain,(
    ! [A_139,A_63] :
      ( k5_relat_1(k6_relat_1(A_139),k6_relat_1(A_63)) = k6_relat_1(A_63)
      | ~ r1_tarski(A_63,A_139)
      | ~ v1_relat_1(k6_relat_1(A_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_602])).

tff(c_1318,plain,(
    ! [A_195,A_196] :
      ( k5_relat_1(k6_relat_1(A_195),k6_relat_1(A_196)) = k6_relat_1(A_196)
      | ~ r1_tarski(A_196,A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_611])).

tff(c_60,plain,(
    ! [A_73,B_74] :
      ( k5_relat_1(k6_relat_1(A_73),B_74) = k7_relat_1(B_74,A_73)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1334,plain,(
    ! [A_196,A_195] :
      ( k7_relat_1(k6_relat_1(A_196),A_195) = k6_relat_1(A_196)
      | ~ v1_relat_1(k6_relat_1(A_196))
      | ~ r1_tarski(A_196,A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1318,c_60])).

tff(c_1389,plain,(
    ! [A_196,A_195] :
      ( k7_relat_1(k6_relat_1(A_196),A_195) = k6_relat_1(A_196)
      | ~ r1_tarski(A_196,A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1334])).

tff(c_10573,plain,(
    ! [A_490,A_489] :
      ( k7_relat_1(k6_relat_1(A_490),A_489) = k6_relat_1(A_489)
      | ~ r1_tarski(A_489,A_490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10230,c_1389])).

tff(c_621,plain,(
    ! [B_140] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_140)),B_140) = B_140
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_6,c_602])).

tff(c_6341,plain,(
    ! [B_380,A_381,A_382] :
      ( k5_relat_1(B_380,k7_relat_1(k6_relat_1(A_381),A_382)) = k8_relat_1(A_381,k8_relat_1(A_382,B_380))
      | ~ v1_relat_1(B_380) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_331,c_1842])).

tff(c_6416,plain,(
    ! [A_381,A_382] :
      ( k8_relat_1(A_381,k8_relat_1(A_382,k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_381),A_382))))) = k7_relat_1(k6_relat_1(A_381),A_382)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_381),A_382))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_381),A_382)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_6341])).

tff(c_47210,plain,(
    ! [A_934,A_935] : k8_relat_1(A_934,k7_relat_1(k6_relat_1(A_935),k3_xboole_0(A_934,A_935))) = k7_relat_1(k6_relat_1(A_934),A_935) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_26,c_507,c_331,c_6416])).

tff(c_47307,plain,(
    ! [A_934,A_490] :
      ( k8_relat_1(A_934,k6_relat_1(k3_xboole_0(A_934,A_490))) = k7_relat_1(k6_relat_1(A_934),A_490)
      | ~ r1_tarski(k3_xboole_0(A_934,A_490),A_490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10573,c_47210])).

tff(c_47509,plain,(
    ! [A_939,A_940] : k7_relat_1(k6_relat_1(A_939),k3_xboole_0(A_939,A_940)) = k7_relat_1(k6_relat_1(A_939),A_940) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10758,c_331,c_47307])).

tff(c_47632,plain,(
    ! [A_939,A_940] :
      ( k7_relat_1(k6_relat_1(A_939),A_940) = k6_relat_1(k3_xboole_0(A_939,A_940))
      | ~ r1_tarski(k3_xboole_0(A_939,A_940),A_939) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47509,c_10573])).

tff(c_47936,plain,(
    ! [A_939,A_940] : k7_relat_1(k6_relat_1(A_939),A_940) = k6_relat_1(k3_xboole_0(A_939,A_940)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_47632])).

tff(c_62,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_294,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_62])).

tff(c_324,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_294])).

tff(c_48437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47936,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.25/8.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.25/8.17  
% 16.25/8.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.25/8.17  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 16.25/8.17  
% 16.25/8.17  %Foreground sorts:
% 16.25/8.17  
% 16.25/8.17  
% 16.25/8.17  %Background operators:
% 16.25/8.17  
% 16.25/8.17  
% 16.25/8.17  %Foreground operators:
% 16.25/8.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 16.25/8.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.25/8.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.25/8.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 16.25/8.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.25/8.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.25/8.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.25/8.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.25/8.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.25/8.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.25/8.17  tff('#skF_2', type, '#skF_2': $i).
% 16.25/8.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.25/8.17  tff('#skF_1', type, '#skF_1': $i).
% 16.25/8.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.25/8.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.25/8.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.25/8.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.25/8.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 16.25/8.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.25/8.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.25/8.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.25/8.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.25/8.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.25/8.17  
% 16.34/8.19  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 16.34/8.19  tff(f_113, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 16.34/8.19  tff(f_137, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 16.34/8.19  tff(f_133, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 16.34/8.19  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 16.34/8.19  tff(f_141, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 16.34/8.19  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 16.34/8.19  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 16.34/8.19  tff(f_119, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 16.34/8.19  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 16.34/8.19  tff(f_125, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 16.34/8.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.34/8.19  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.34/8.19  tff(f_144, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 16.34/8.19  tff(c_26, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.34/8.19  tff(c_44, plain, (![A_63]: (k1_relat_1(k6_relat_1(A_63))=A_63)), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.34/8.19  tff(c_494, plain, (![B_129, A_130]: (k3_xboole_0(k1_relat_1(B_129), A_130)=k1_relat_1(k7_relat_1(B_129, A_130)) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.34/8.19  tff(c_503, plain, (![A_63, A_130]: (k1_relat_1(k7_relat_1(k6_relat_1(A_63), A_130))=k3_xboole_0(A_63, A_130) | ~v1_relat_1(k6_relat_1(A_63)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_494])).
% 16.34/8.19  tff(c_507, plain, (![A_63, A_130]: (k1_relat_1(k7_relat_1(k6_relat_1(A_63), A_130))=k3_xboole_0(A_63, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_503])).
% 16.34/8.19  tff(c_181, plain, (![B_96, A_97]: (r1_tarski(k1_relat_1(k7_relat_1(B_96, A_97)), k1_relat_1(B_96)) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_133])).
% 16.34/8.19  tff(c_188, plain, (![A_63, A_97]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_63), A_97)), A_63) | ~v1_relat_1(k6_relat_1(A_63)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_181])).
% 16.34/8.19  tff(c_192, plain, (![A_63, A_97]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_63), A_97)), A_63))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_188])).
% 16.34/8.19  tff(c_508, plain, (![A_63, A_97]: (r1_tarski(k3_xboole_0(A_63, A_97), A_63))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_192])).
% 16.34/8.19  tff(c_30, plain, (![B_43, A_42]: (k5_relat_1(B_43, k6_relat_1(A_42))=k8_relat_1(A_42, B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.34/8.19  tff(c_273, plain, (![A_107, B_108]: (k5_relat_1(k6_relat_1(A_107), B_108)=k7_relat_1(B_108, A_107) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.34/8.19  tff(c_308, plain, (![A_42, A_107]: (k8_relat_1(A_42, k6_relat_1(A_107))=k7_relat_1(k6_relat_1(A_42), A_107) | ~v1_relat_1(k6_relat_1(A_42)) | ~v1_relat_1(k6_relat_1(A_107)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_273])).
% 16.34/8.19  tff(c_402, plain, (![A_117, A_118]: (k8_relat_1(A_117, k6_relat_1(A_118))=k7_relat_1(k6_relat_1(A_117), A_118))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_308])).
% 16.34/8.19  tff(c_193, plain, (![B_98, A_99]: (k5_relat_1(B_98, k6_relat_1(A_99))=k8_relat_1(A_99, B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.34/8.19  tff(c_24, plain, (![A_35, B_36]: (v1_relat_1(k5_relat_1(A_35, B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.34/8.19  tff(c_214, plain, (![A_99, B_98]: (v1_relat_1(k8_relat_1(A_99, B_98)) | ~v1_relat_1(k6_relat_1(A_99)) | ~v1_relat_1(B_98) | ~v1_relat_1(B_98))), inference(superposition, [status(thm), theory('equality')], [c_193, c_24])).
% 16.34/8.19  tff(c_235, plain, (![A_99, B_98]: (v1_relat_1(k8_relat_1(A_99, B_98)) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_214])).
% 16.34/8.19  tff(c_412, plain, (![A_117, A_118]: (v1_relat_1(k7_relat_1(k6_relat_1(A_117), A_118)) | ~v1_relat_1(k6_relat_1(A_118)))), inference(superposition, [status(thm), theory('equality')], [c_402, c_235])).
% 16.34/8.19  tff(c_422, plain, (![A_117, A_118]: (v1_relat_1(k7_relat_1(k6_relat_1(A_117), A_118)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_412])).
% 16.34/8.19  tff(c_331, plain, (![A_42, A_107]: (k8_relat_1(A_42, k6_relat_1(A_107))=k7_relat_1(k6_relat_1(A_42), A_107))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_308])).
% 16.34/8.19  tff(c_1807, plain, (![A_212, B_213, C_214]: (k8_relat_1(A_212, k5_relat_1(B_213, C_214))=k5_relat_1(B_213, k8_relat_1(A_212, C_214)) | ~v1_relat_1(C_214) | ~v1_relat_1(B_213))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.34/8.19  tff(c_1842, plain, (![B_43, A_212, A_42]: (k5_relat_1(B_43, k8_relat_1(A_212, k6_relat_1(A_42)))=k8_relat_1(A_212, k8_relat_1(A_42, B_43)) | ~v1_relat_1(k6_relat_1(A_42)) | ~v1_relat_1(B_43) | ~v1_relat_1(B_43))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1807])).
% 16.34/8.19  tff(c_1858, plain, (![B_43, A_212, A_42]: (k5_relat_1(B_43, k7_relat_1(k6_relat_1(A_212), A_42))=k8_relat_1(A_212, k8_relat_1(A_42, B_43)) | ~v1_relat_1(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_331, c_1842])).
% 16.34/8.19  tff(c_48, plain, (![A_64, B_65]: (r1_tarski(k5_relat_1(k6_relat_1(A_64), B_65), B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_119])).
% 16.34/8.19  tff(c_200, plain, (![A_99, A_64]: (r1_tarski(k8_relat_1(A_99, k6_relat_1(A_64)), k6_relat_1(A_99)) | ~v1_relat_1(k6_relat_1(A_99)) | ~v1_relat_1(k6_relat_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_48])).
% 16.34/8.19  tff(c_229, plain, (![A_99, A_64]: (r1_tarski(k8_relat_1(A_99, k6_relat_1(A_64)), k6_relat_1(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_200])).
% 16.34/8.19  tff(c_400, plain, (![A_99, A_64]: (r1_tarski(k7_relat_1(k6_relat_1(A_99), A_64), k6_relat_1(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_229])).
% 16.34/8.19  tff(c_988, plain, (![A_167, B_168]: (r1_tarski(k1_relat_1(A_167), k1_relat_1(B_168)) | ~r1_tarski(A_167, B_168) | ~v1_relat_1(B_168) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.34/8.19  tff(c_1007, plain, (![A_167, A_63]: (r1_tarski(k1_relat_1(A_167), A_63) | ~r1_tarski(A_167, k6_relat_1(A_63)) | ~v1_relat_1(k6_relat_1(A_63)) | ~v1_relat_1(A_167))), inference(superposition, [status(thm), theory('equality')], [c_44, c_988])).
% 16.34/8.19  tff(c_1863, plain, (![A_215, A_216]: (r1_tarski(k1_relat_1(A_215), A_216) | ~r1_tarski(A_215, k6_relat_1(A_216)) | ~v1_relat_1(A_215))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1007])).
% 16.34/8.19  tff(c_52, plain, (![A_66, B_67]: (k5_relat_1(k6_relat_1(A_66), B_67)=B_67 | ~r1_tarski(k1_relat_1(B_67), A_66) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.34/8.19  tff(c_4329, plain, (![A_327, A_328]: (k5_relat_1(k6_relat_1(A_327), A_328)=A_328 | ~r1_tarski(A_328, k6_relat_1(A_327)) | ~v1_relat_1(A_328))), inference(resolution, [status(thm)], [c_1863, c_52])).
% 16.34/8.19  tff(c_4457, plain, (![A_99, A_64]: (k5_relat_1(k6_relat_1(A_99), k7_relat_1(k6_relat_1(A_99), A_64))=k7_relat_1(k6_relat_1(A_99), A_64) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_99), A_64)))), inference(resolution, [status(thm)], [c_400, c_4329])).
% 16.34/8.19  tff(c_9463, plain, (![A_467, A_468]: (k5_relat_1(k6_relat_1(A_467), k7_relat_1(k6_relat_1(A_467), A_468))=k7_relat_1(k6_relat_1(A_467), A_468))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_4457])).
% 16.34/8.19  tff(c_9532, plain, (![A_212, A_42]: (k8_relat_1(A_212, k8_relat_1(A_42, k6_relat_1(A_212)))=k7_relat_1(k6_relat_1(A_212), A_42) | ~v1_relat_1(k6_relat_1(A_212)))), inference(superposition, [status(thm), theory('equality')], [c_1858, c_9463])).
% 16.34/8.19  tff(c_10056, plain, (![A_485, A_486]: (k8_relat_1(A_485, k7_relat_1(k6_relat_1(A_486), A_485))=k7_relat_1(k6_relat_1(A_485), A_486))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_331, c_9532])).
% 16.34/8.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.34/8.19  tff(c_50, plain, (![B_65, A_64]: (r1_tarski(k5_relat_1(B_65, k6_relat_1(A_64)), B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_119])).
% 16.34/8.19  tff(c_827, plain, (![A_156, B_157]: (r1_tarski(k8_relat_1(A_156, B_157), B_157) | ~v1_relat_1(B_157) | ~v1_relat_1(B_157))), inference(superposition, [status(thm), theory('equality')], [c_193, c_50])).
% 16.34/8.19  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.34/8.19  tff(c_1974, plain, (![A_229, B_230, A_231]: (r1_tarski(A_229, B_230) | ~r1_tarski(A_229, k8_relat_1(A_231, B_230)) | ~v1_relat_1(B_230))), inference(resolution, [status(thm)], [c_827, c_8])).
% 16.34/8.19  tff(c_2080, plain, (![A_231, B_230]: (r1_tarski(k8_relat_1(A_231, B_230), B_230) | ~v1_relat_1(B_230))), inference(resolution, [status(thm)], [c_6, c_1974])).
% 16.34/8.19  tff(c_10108, plain, (![A_485, A_486]: (r1_tarski(k7_relat_1(k6_relat_1(A_485), A_486), k7_relat_1(k6_relat_1(A_486), A_485)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_486), A_485)))), inference(superposition, [status(thm), theory('equality')], [c_10056, c_2080])).
% 16.34/8.19  tff(c_10161, plain, (![A_485, A_486]: (r1_tarski(k7_relat_1(k6_relat_1(A_485), A_486), k7_relat_1(k6_relat_1(A_486), A_485)))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_10108])).
% 16.34/8.19  tff(c_10174, plain, (![A_487, A_488]: (r1_tarski(k7_relat_1(k6_relat_1(A_487), A_488), k7_relat_1(k6_relat_1(A_488), A_487)))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_10108])).
% 16.34/8.19  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.34/8.19  tff(c_10190, plain, (![A_488, A_487]: (k7_relat_1(k6_relat_1(A_488), A_487)=k7_relat_1(k6_relat_1(A_487), A_488) | ~r1_tarski(k7_relat_1(k6_relat_1(A_488), A_487), k7_relat_1(k6_relat_1(A_487), A_488)))), inference(resolution, [status(thm)], [c_10174, c_2])).
% 16.34/8.19  tff(c_10230, plain, (![A_490, A_489]: (k7_relat_1(k6_relat_1(A_490), A_489)=k7_relat_1(k6_relat_1(A_489), A_490))), inference(demodulation, [status(thm), theory('equality')], [c_10161, c_10190])).
% 16.34/8.19  tff(c_56, plain, (![B_70, A_69]: (r1_tarski(k1_relat_1(k7_relat_1(B_70, A_69)), k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_133])).
% 16.34/8.19  tff(c_10633, plain, (![A_490, A_489]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_490), A_489)), k1_relat_1(k6_relat_1(A_489))) | ~v1_relat_1(k6_relat_1(A_489)))), inference(superposition, [status(thm), theory('equality')], [c_10230, c_56])).
% 16.34/8.19  tff(c_10758, plain, (![A_490, A_489]: (r1_tarski(k3_xboole_0(A_490, A_489), A_489))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_507, c_44, c_10633])).
% 16.34/8.19  tff(c_602, plain, (![A_139, B_140]: (k5_relat_1(k6_relat_1(A_139), B_140)=B_140 | ~r1_tarski(k1_relat_1(B_140), A_139) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.34/8.19  tff(c_611, plain, (![A_139, A_63]: (k5_relat_1(k6_relat_1(A_139), k6_relat_1(A_63))=k6_relat_1(A_63) | ~r1_tarski(A_63, A_139) | ~v1_relat_1(k6_relat_1(A_63)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_602])).
% 16.34/8.19  tff(c_1318, plain, (![A_195, A_196]: (k5_relat_1(k6_relat_1(A_195), k6_relat_1(A_196))=k6_relat_1(A_196) | ~r1_tarski(A_196, A_195))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_611])).
% 16.34/8.19  tff(c_60, plain, (![A_73, B_74]: (k5_relat_1(k6_relat_1(A_73), B_74)=k7_relat_1(B_74, A_73) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.34/8.19  tff(c_1334, plain, (![A_196, A_195]: (k7_relat_1(k6_relat_1(A_196), A_195)=k6_relat_1(A_196) | ~v1_relat_1(k6_relat_1(A_196)) | ~r1_tarski(A_196, A_195))), inference(superposition, [status(thm), theory('equality')], [c_1318, c_60])).
% 16.34/8.19  tff(c_1389, plain, (![A_196, A_195]: (k7_relat_1(k6_relat_1(A_196), A_195)=k6_relat_1(A_196) | ~r1_tarski(A_196, A_195))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1334])).
% 16.34/8.19  tff(c_10573, plain, (![A_490, A_489]: (k7_relat_1(k6_relat_1(A_490), A_489)=k6_relat_1(A_489) | ~r1_tarski(A_489, A_490))), inference(superposition, [status(thm), theory('equality')], [c_10230, c_1389])).
% 16.34/8.19  tff(c_621, plain, (![B_140]: (k5_relat_1(k6_relat_1(k1_relat_1(B_140)), B_140)=B_140 | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_6, c_602])).
% 16.34/8.19  tff(c_6341, plain, (![B_380, A_381, A_382]: (k5_relat_1(B_380, k7_relat_1(k6_relat_1(A_381), A_382))=k8_relat_1(A_381, k8_relat_1(A_382, B_380)) | ~v1_relat_1(B_380))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_331, c_1842])).
% 16.34/8.19  tff(c_6416, plain, (![A_381, A_382]: (k8_relat_1(A_381, k8_relat_1(A_382, k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_381), A_382)))))=k7_relat_1(k6_relat_1(A_381), A_382) | ~v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_381), A_382)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_381), A_382)))), inference(superposition, [status(thm), theory('equality')], [c_621, c_6341])).
% 16.34/8.19  tff(c_47210, plain, (![A_934, A_935]: (k8_relat_1(A_934, k7_relat_1(k6_relat_1(A_935), k3_xboole_0(A_934, A_935)))=k7_relat_1(k6_relat_1(A_934), A_935))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_26, c_507, c_331, c_6416])).
% 16.34/8.19  tff(c_47307, plain, (![A_934, A_490]: (k8_relat_1(A_934, k6_relat_1(k3_xboole_0(A_934, A_490)))=k7_relat_1(k6_relat_1(A_934), A_490) | ~r1_tarski(k3_xboole_0(A_934, A_490), A_490))), inference(superposition, [status(thm), theory('equality')], [c_10573, c_47210])).
% 16.34/8.19  tff(c_47509, plain, (![A_939, A_940]: (k7_relat_1(k6_relat_1(A_939), k3_xboole_0(A_939, A_940))=k7_relat_1(k6_relat_1(A_939), A_940))), inference(demodulation, [status(thm), theory('equality')], [c_10758, c_331, c_47307])).
% 16.34/8.19  tff(c_47632, plain, (![A_939, A_940]: (k7_relat_1(k6_relat_1(A_939), A_940)=k6_relat_1(k3_xboole_0(A_939, A_940)) | ~r1_tarski(k3_xboole_0(A_939, A_940), A_939))), inference(superposition, [status(thm), theory('equality')], [c_47509, c_10573])).
% 16.34/8.19  tff(c_47936, plain, (![A_939, A_940]: (k7_relat_1(k6_relat_1(A_939), A_940)=k6_relat_1(k3_xboole_0(A_939, A_940)))), inference(demodulation, [status(thm), theory('equality')], [c_508, c_47632])).
% 16.34/8.19  tff(c_62, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 16.34/8.19  tff(c_294, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_62])).
% 16.34/8.19  tff(c_324, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_294])).
% 16.34/8.19  tff(c_48437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47936, c_324])).
% 16.34/8.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.34/8.19  
% 16.34/8.19  Inference rules
% 16.34/8.19  ----------------------
% 16.34/8.19  #Ref     : 0
% 16.34/8.19  #Sup     : 11109
% 16.34/8.19  #Fact    : 0
% 16.34/8.19  #Define  : 0
% 16.34/8.19  #Split   : 2
% 16.34/8.19  #Chain   : 0
% 16.34/8.19  #Close   : 0
% 16.34/8.19  
% 16.34/8.19  Ordering : KBO
% 16.34/8.19  
% 16.34/8.19  Simplification rules
% 16.34/8.19  ----------------------
% 16.34/8.19  #Subsume      : 1122
% 16.34/8.19  #Demod        : 7443
% 16.34/8.19  #Tautology    : 3110
% 16.34/8.19  #SimpNegUnit  : 0
% 16.34/8.19  #BackRed      : 93
% 16.34/8.19  
% 16.34/8.19  #Partial instantiations: 0
% 16.34/8.19  #Strategies tried      : 1
% 16.34/8.19  
% 16.34/8.19  Timing (in seconds)
% 16.34/8.19  ----------------------
% 16.34/8.20  Preprocessing        : 0.36
% 16.34/8.20  Parsing              : 0.19
% 16.34/8.20  CNF conversion       : 0.02
% 16.34/8.20  Main loop            : 7.08
% 16.34/8.20  Inferencing          : 1.18
% 16.34/8.20  Reduction            : 3.11
% 16.34/8.20  Demodulation         : 2.69
% 16.34/8.20  BG Simplification    : 0.18
% 16.34/8.20  Subsumption          : 2.16
% 16.34/8.20  Abstraction          : 0.23
% 16.34/8.20  MUC search           : 0.00
% 16.34/8.20  Cooper               : 0.00
% 16.34/8.20  Total                : 7.48
% 16.34/8.20  Index Insertion      : 0.00
% 16.34/8.20  Index Deletion       : 0.00
% 16.34/8.20  Index Matching       : 0.00
% 16.34/8.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
