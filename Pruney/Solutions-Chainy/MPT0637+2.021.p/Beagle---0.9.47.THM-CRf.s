%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:27 EST 2020

% Result     : Theorem 10.69s
% Output     : CNFRefutation 10.73s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 155 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 237 expanded)
%              Number of equality atoms :   45 (  86 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    ! [B_45,A_46] : k1_setfam_1(k2_tarski(B_45,A_46)) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_102])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_10])).

tff(c_164,plain,(
    ! [B_47,A_48] : r1_tarski(k3_xboole_0(B_47,A_48),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2])).

tff(c_34,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_24] : k1_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_477,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = B_78
      | ~ r1_tarski(k1_relat_1(B_78),A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_484,plain,(
    ! [A_24,A_79] :
      ( k7_relat_1(k6_relat_1(A_24),A_79) = k6_relat_1(A_24)
      | ~ r1_tarski(A_24,A_79)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_477])).

tff(c_487,plain,(
    ! [A_24,A_79] :
      ( k7_relat_1(k6_relat_1(A_24),A_79) = k6_relat_1(A_24)
      | ~ r1_tarski(A_24,A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_484])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_relat_1(A_27),B_28) = k7_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_302,plain,(
    ! [B_63,A_64] :
      ( k5_relat_1(B_63,k6_relat_1(A_64)) = k8_relat_1(A_64,B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_330,plain,(
    ! [A_64,A_27] :
      ( k8_relat_1(A_64,k6_relat_1(A_27)) = k7_relat_1(k6_relat_1(A_64),A_27)
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_302])).

tff(c_368,plain,(
    ! [A_68,A_69] : k8_relat_1(A_68,k6_relat_1(A_69)) = k7_relat_1(k6_relat_1(A_68),A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_330])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k5_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_320,plain,(
    ! [A_64,B_63] :
      ( v1_relat_1(k8_relat_1(A_64,B_63))
      | ~ v1_relat_1(k6_relat_1(A_64))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_12])).

tff(c_343,plain,(
    ! [A_64,B_63] :
      ( v1_relat_1(k8_relat_1(A_64,B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_320])).

tff(c_378,plain,(
    ! [A_68,A_69] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_68),A_69))
      | ~ v1_relat_1(k6_relat_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_343])).

tff(c_388,plain,(
    ! [A_68,A_69] : v1_relat_1(k7_relat_1(k6_relat_1(A_68),A_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_378])).

tff(c_348,plain,(
    ! [A_64,A_27] : k8_relat_1(A_64,k6_relat_1(A_27)) = k7_relat_1(k6_relat_1(A_64),A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_330])).

tff(c_24,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_396,plain,(
    ! [B_72,A_73] :
      ( k3_xboole_0(k2_relat_1(B_72),A_73) = k2_relat_1(k8_relat_1(A_73,B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_425,plain,(
    ! [A_73,A_24] :
      ( k2_relat_1(k8_relat_1(A_73,k6_relat_1(A_24))) = k3_xboole_0(A_24,A_73)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_396])).

tff(c_429,plain,(
    ! [A_73,A_24] : k2_relat_1(k7_relat_1(k6_relat_1(A_73),A_24)) = k3_xboole_0(A_24,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_348,c_425])).

tff(c_618,plain,(
    ! [A_86,C_87,B_88] :
      ( k8_relat_1(A_86,k7_relat_1(C_87,B_88)) = k7_relat_1(k8_relat_1(A_86,C_87),B_88)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_26] :
      ( k5_relat_1(A_26,k6_relat_1(k2_relat_1(A_26))) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_336,plain,(
    ! [A_26] :
      ( k8_relat_1(k2_relat_1(A_26),A_26) = A_26
      | ~ v1_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_302])).

tff(c_16107,plain,(
    ! [C_322,B_323] :
      ( k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(C_322,B_323)),C_322),B_323) = k7_relat_1(C_322,B_323)
      | ~ v1_relat_1(k7_relat_1(C_322,B_323))
      | ~ v1_relat_1(k7_relat_1(C_322,B_323))
      | ~ v1_relat_1(C_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_336])).

tff(c_16185,plain,(
    ! [A_24,A_73] :
      ( k7_relat_1(k8_relat_1(k3_xboole_0(A_24,A_73),k6_relat_1(A_73)),A_24) = k7_relat_1(k6_relat_1(A_73),A_24)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_73),A_24))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_73),A_24))
      | ~ v1_relat_1(k6_relat_1(A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_16107])).

tff(c_20533,plain,(
    ! [A_361,A_362] : k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_361,A_362)),A_362),A_361) = k7_relat_1(k6_relat_1(A_362),A_361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_388,c_388,c_348,c_16185])).

tff(c_20697,plain,(
    ! [A_361,A_79] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_361,A_79)),A_361) = k7_relat_1(k6_relat_1(A_79),A_361)
      | ~ r1_tarski(k3_xboole_0(A_361,A_79),A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_20533])).

tff(c_20741,plain,(
    ! [A_363,A_364] : k7_relat_1(k6_relat_1(k3_xboole_0(A_363,A_364)),A_363) = k7_relat_1(k6_relat_1(A_364),A_363) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_20697])).

tff(c_20805,plain,(
    ! [A_364,A_363] :
      ( k7_relat_1(k6_relat_1(A_364),A_363) = k6_relat_1(k3_xboole_0(A_363,A_364))
      | ~ r1_tarski(k3_xboole_0(A_363,A_364),A_363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20741,c_487])).

tff(c_20967,plain,(
    ! [A_364,A_363] : k7_relat_1(k6_relat_1(A_364),A_363) = k6_relat_1(k3_xboole_0(A_363,A_364)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20805])).

tff(c_233,plain,(
    ! [A_55,B_56] :
      ( k5_relat_1(k6_relat_1(A_55),B_56) = k7_relat_1(B_56,A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_250,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_38])).

tff(c_269,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_250])).

tff(c_21016,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20967,c_269])).

tff(c_21035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_21016])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.69/4.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.69/4.49  
% 10.69/4.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.69/4.49  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 10.69/4.49  
% 10.69/4.49  %Foreground sorts:
% 10.69/4.49  
% 10.69/4.49  
% 10.69/4.49  %Background operators:
% 10.69/4.49  
% 10.69/4.49  
% 10.69/4.49  %Foreground operators:
% 10.69/4.49  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 10.69/4.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.69/4.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.69/4.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.69/4.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.69/4.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.69/4.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.69/4.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.69/4.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.69/4.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.69/4.49  tff('#skF_2', type, '#skF_2': $i).
% 10.69/4.49  tff('#skF_1', type, '#skF_1': $i).
% 10.69/4.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.69/4.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.69/4.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.69/4.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.69/4.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.69/4.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.69/4.49  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.69/4.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.69/4.49  
% 10.73/4.51  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.73/4.51  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.73/4.51  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.73/4.51  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.73/4.51  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.73/4.51  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 10.73/4.51  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 10.73/4.51  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 10.73/4.51  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 10.73/4.51  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 10.73/4.51  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 10.73/4.51  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 10.73/4.51  tff(f_87, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 10.73/4.51  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.73/4.51  tff(c_102, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.73/4.51  tff(c_126, plain, (![B_45, A_46]: (k1_setfam_1(k2_tarski(B_45, A_46))=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_4, c_102])).
% 10.73/4.51  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.73/4.51  tff(c_132, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_126, c_10])).
% 10.73/4.51  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.73/4.51  tff(c_149, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_126, c_10])).
% 10.73/4.51  tff(c_164, plain, (![B_47, A_48]: (r1_tarski(k3_xboole_0(B_47, A_48), A_48))), inference(superposition, [status(thm), theory('equality')], [c_149, c_2])).
% 10.73/4.51  tff(c_34, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.73/4.51  tff(c_22, plain, (![A_24]: (k1_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.73/4.51  tff(c_477, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=B_78 | ~r1_tarski(k1_relat_1(B_78), A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.73/4.51  tff(c_484, plain, (![A_24, A_79]: (k7_relat_1(k6_relat_1(A_24), A_79)=k6_relat_1(A_24) | ~r1_tarski(A_24, A_79) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_477])).
% 10.73/4.51  tff(c_487, plain, (![A_24, A_79]: (k7_relat_1(k6_relat_1(A_24), A_79)=k6_relat_1(A_24) | ~r1_tarski(A_24, A_79))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_484])).
% 10.73/4.51  tff(c_30, plain, (![A_27, B_28]: (k5_relat_1(k6_relat_1(A_27), B_28)=k7_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.73/4.51  tff(c_302, plain, (![B_63, A_64]: (k5_relat_1(B_63, k6_relat_1(A_64))=k8_relat_1(A_64, B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.73/4.51  tff(c_330, plain, (![A_64, A_27]: (k8_relat_1(A_64, k6_relat_1(A_27))=k7_relat_1(k6_relat_1(A_64), A_27) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_302])).
% 10.73/4.51  tff(c_368, plain, (![A_68, A_69]: (k8_relat_1(A_68, k6_relat_1(A_69))=k7_relat_1(k6_relat_1(A_68), A_69))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_330])).
% 10.73/4.51  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.73/4.51  tff(c_320, plain, (![A_64, B_63]: (v1_relat_1(k8_relat_1(A_64, B_63)) | ~v1_relat_1(k6_relat_1(A_64)) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_302, c_12])).
% 10.73/4.51  tff(c_343, plain, (![A_64, B_63]: (v1_relat_1(k8_relat_1(A_64, B_63)) | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_320])).
% 10.73/4.51  tff(c_378, plain, (![A_68, A_69]: (v1_relat_1(k7_relat_1(k6_relat_1(A_68), A_69)) | ~v1_relat_1(k6_relat_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_368, c_343])).
% 10.73/4.51  tff(c_388, plain, (![A_68, A_69]: (v1_relat_1(k7_relat_1(k6_relat_1(A_68), A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_378])).
% 10.73/4.51  tff(c_348, plain, (![A_64, A_27]: (k8_relat_1(A_64, k6_relat_1(A_27))=k7_relat_1(k6_relat_1(A_64), A_27))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_330])).
% 10.73/4.51  tff(c_24, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.73/4.51  tff(c_396, plain, (![B_72, A_73]: (k3_xboole_0(k2_relat_1(B_72), A_73)=k2_relat_1(k8_relat_1(A_73, B_72)) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.73/4.51  tff(c_425, plain, (![A_73, A_24]: (k2_relat_1(k8_relat_1(A_73, k6_relat_1(A_24)))=k3_xboole_0(A_24, A_73) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_396])).
% 10.73/4.51  tff(c_429, plain, (![A_73, A_24]: (k2_relat_1(k7_relat_1(k6_relat_1(A_73), A_24))=k3_xboole_0(A_24, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_348, c_425])).
% 10.73/4.51  tff(c_618, plain, (![A_86, C_87, B_88]: (k8_relat_1(A_86, k7_relat_1(C_87, B_88))=k7_relat_1(k8_relat_1(A_86, C_87), B_88) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.73/4.51  tff(c_28, plain, (![A_26]: (k5_relat_1(A_26, k6_relat_1(k2_relat_1(A_26)))=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.73/4.51  tff(c_336, plain, (![A_26]: (k8_relat_1(k2_relat_1(A_26), A_26)=A_26 | ~v1_relat_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_28, c_302])).
% 10.73/4.51  tff(c_16107, plain, (![C_322, B_323]: (k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(C_322, B_323)), C_322), B_323)=k7_relat_1(C_322, B_323) | ~v1_relat_1(k7_relat_1(C_322, B_323)) | ~v1_relat_1(k7_relat_1(C_322, B_323)) | ~v1_relat_1(C_322))), inference(superposition, [status(thm), theory('equality')], [c_618, c_336])).
% 10.73/4.51  tff(c_16185, plain, (![A_24, A_73]: (k7_relat_1(k8_relat_1(k3_xboole_0(A_24, A_73), k6_relat_1(A_73)), A_24)=k7_relat_1(k6_relat_1(A_73), A_24) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_73), A_24)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_73), A_24)) | ~v1_relat_1(k6_relat_1(A_73)))), inference(superposition, [status(thm), theory('equality')], [c_429, c_16107])).
% 10.73/4.51  tff(c_20533, plain, (![A_361, A_362]: (k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_361, A_362)), A_362), A_361)=k7_relat_1(k6_relat_1(A_362), A_361))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_388, c_388, c_348, c_16185])).
% 10.73/4.51  tff(c_20697, plain, (![A_361, A_79]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_361, A_79)), A_361)=k7_relat_1(k6_relat_1(A_79), A_361) | ~r1_tarski(k3_xboole_0(A_361, A_79), A_79))), inference(superposition, [status(thm), theory('equality')], [c_487, c_20533])).
% 10.73/4.51  tff(c_20741, plain, (![A_363, A_364]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_363, A_364)), A_363)=k7_relat_1(k6_relat_1(A_364), A_363))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_20697])).
% 10.73/4.51  tff(c_20805, plain, (![A_364, A_363]: (k7_relat_1(k6_relat_1(A_364), A_363)=k6_relat_1(k3_xboole_0(A_363, A_364)) | ~r1_tarski(k3_xboole_0(A_363, A_364), A_363))), inference(superposition, [status(thm), theory('equality')], [c_20741, c_487])).
% 10.73/4.51  tff(c_20967, plain, (![A_364, A_363]: (k7_relat_1(k6_relat_1(A_364), A_363)=k6_relat_1(k3_xboole_0(A_363, A_364)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20805])).
% 10.73/4.51  tff(c_233, plain, (![A_55, B_56]: (k5_relat_1(k6_relat_1(A_55), B_56)=k7_relat_1(B_56, A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.73/4.51  tff(c_38, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.73/4.51  tff(c_250, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_233, c_38])).
% 10.73/4.51  tff(c_269, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_250])).
% 10.73/4.51  tff(c_21016, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20967, c_269])).
% 10.73/4.51  tff(c_21035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_21016])).
% 10.73/4.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.73/4.51  
% 10.73/4.51  Inference rules
% 10.73/4.51  ----------------------
% 10.73/4.51  #Ref     : 0
% 10.73/4.51  #Sup     : 5525
% 10.73/4.51  #Fact    : 0
% 10.73/4.51  #Define  : 0
% 10.73/4.51  #Split   : 2
% 10.73/4.51  #Chain   : 0
% 10.73/4.51  #Close   : 0
% 10.73/4.51  
% 10.73/4.51  Ordering : KBO
% 10.73/4.51  
% 10.73/4.51  Simplification rules
% 10.73/4.51  ----------------------
% 10.73/4.51  #Subsume      : 897
% 10.73/4.51  #Demod        : 4591
% 10.73/4.51  #Tautology    : 1626
% 10.73/4.51  #SimpNegUnit  : 0
% 10.73/4.51  #BackRed      : 36
% 10.73/4.51  
% 10.73/4.51  #Partial instantiations: 0
% 10.73/4.51  #Strategies tried      : 1
% 10.73/4.51  
% 10.73/4.51  Timing (in seconds)
% 10.73/4.51  ----------------------
% 10.73/4.51  Preprocessing        : 0.31
% 10.73/4.51  Parsing              : 0.16
% 10.81/4.51  CNF conversion       : 0.02
% 10.82/4.51  Main loop            : 3.40
% 10.82/4.51  Inferencing          : 0.68
% 10.82/4.51  Reduction            : 1.75
% 10.82/4.51  Demodulation         : 1.56
% 10.82/4.51  BG Simplification    : 0.11
% 10.82/4.51  Subsumption          : 0.70
% 10.82/4.51  Abstraction          : 0.15
% 10.82/4.51  MUC search           : 0.00
% 10.82/4.51  Cooper               : 0.00
% 10.82/4.51  Total                : 3.75
% 10.82/4.51  Index Insertion      : 0.00
% 10.82/4.51  Index Deletion       : 0.00
% 10.82/4.51  Index Matching       : 0.00
% 10.82/4.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
