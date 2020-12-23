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
% DateTime   : Thu Dec  3 10:03:27 EST 2020

% Result     : Theorem 14.74s
% Output     : CNFRefutation 14.74s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 105 expanded)
%              Number of leaves         :   33 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 132 expanded)
%              Number of equality atoms :   45 (  58 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [B_44,A_45] : k1_setfam_1(k2_tarski(B_44,A_45)) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_98])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_136,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [B_46,A_47] : r1_tarski(k3_xboole_0(B_46,A_47),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2])).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_222,plain,(
    ! [B_57,A_58] :
      ( k5_relat_1(B_57,k6_relat_1(A_58)) = k8_relat_1(A_58,B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( k5_relat_1(k6_relat_1(A_27),B_28) = k7_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_229,plain,(
    ! [A_58,A_27] :
      ( k8_relat_1(A_58,k6_relat_1(A_27)) = k7_relat_1(k6_relat_1(A_58),A_27)
      | ~ v1_relat_1(k6_relat_1(A_58))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_30])).

tff(c_242,plain,(
    ! [A_58,A_27] : k8_relat_1(A_58,k6_relat_1(A_27)) = k7_relat_1(k6_relat_1(A_58),A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_229])).

tff(c_348,plain,(
    ! [B_71,A_72] :
      ( k3_xboole_0(B_71,k2_zfmisc_1(k1_relat_1(B_71),A_72)) = k8_relat_1(A_72,B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_392,plain,(
    ! [A_77,B_78] :
      ( v1_relat_1(k8_relat_1(A_77,B_78))
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_14])).

tff(c_395,plain,(
    ! [A_58,A_27] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_58),A_27))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_392])).

tff(c_397,plain,(
    ! [A_58,A_27] : v1_relat_1(k7_relat_1(k6_relat_1(A_58),A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_395])).

tff(c_22,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_259,plain,(
    ! [B_61,A_62] :
      ( k3_xboole_0(k1_relat_1(B_61),A_62) = k1_relat_1(k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_330,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_69,A_70)),k1_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_2])).

tff(c_32,plain,(
    ! [B_30,A_29] :
      ( k7_relat_1(B_30,A_29) = B_30
      | ~ r1_tarski(k1_relat_1(B_30),A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3327,plain,(
    ! [B_171,A_172] :
      ( k7_relat_1(k7_relat_1(B_171,A_172),k1_relat_1(B_171)) = k7_relat_1(B_171,A_172)
      | ~ v1_relat_1(k7_relat_1(B_171,A_172))
      | ~ v1_relat_1(B_171) ) ),
    inference(resolution,[status(thm)],[c_330,c_32])).

tff(c_3396,plain,(
    ! [A_22,A_172] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_22),A_172),A_22) = k7_relat_1(k6_relat_1(A_22),A_172)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_22),A_172))
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3327])).

tff(c_3889,plain,(
    ! [A_181,A_182] : k7_relat_1(k7_relat_1(k6_relat_1(A_181),A_182),A_181) = k7_relat_1(k6_relat_1(A_181),A_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_397,c_3396])).

tff(c_16,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_17,A_15),B_16) = k7_relat_1(C_17,k3_xboole_0(A_15,B_16))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3918,plain,(
    ! [A_181,A_182] :
      ( k7_relat_1(k6_relat_1(A_181),k3_xboole_0(A_182,A_181)) = k7_relat_1(k6_relat_1(A_181),A_182)
      | ~ v1_relat_1(k6_relat_1(A_181)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3889,c_16])).

tff(c_39571,plain,(
    ! [A_722,A_723] : k7_relat_1(k6_relat_1(A_722),k3_xboole_0(A_723,A_722)) = k7_relat_1(k6_relat_1(A_722),A_723) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3918])).

tff(c_24,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_431,plain,(
    ! [B_83,A_84] :
      ( k5_relat_1(B_83,k6_relat_1(A_84)) = B_83
      | ~ r1_tarski(k2_relat_1(B_83),A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_434,plain,(
    ! [A_22,A_84] :
      ( k5_relat_1(k6_relat_1(A_22),k6_relat_1(A_84)) = k6_relat_1(A_22)
      | ~ r1_tarski(A_22,A_84)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_431])).

tff(c_1673,plain,(
    ! [A_128,A_129] :
      ( k5_relat_1(k6_relat_1(A_128),k6_relat_1(A_129)) = k6_relat_1(A_128)
      | ~ r1_tarski(A_128,A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_434])).

tff(c_1682,plain,(
    ! [A_129,A_128] :
      ( k7_relat_1(k6_relat_1(A_129),A_128) = k6_relat_1(A_128)
      | ~ v1_relat_1(k6_relat_1(A_129))
      | ~ r1_tarski(A_128,A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_30])).

tff(c_1701,plain,(
    ! [A_129,A_128] :
      ( k7_relat_1(k6_relat_1(A_129),A_128) = k6_relat_1(A_128)
      | ~ r1_tarski(A_128,A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1682])).

tff(c_39781,plain,(
    ! [A_722,A_723] :
      ( k7_relat_1(k6_relat_1(A_722),A_723) = k6_relat_1(k3_xboole_0(A_723,A_722))
      | ~ r1_tarski(k3_xboole_0(A_723,A_722),A_722) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39571,c_1701])).

tff(c_40031,plain,(
    ! [A_722,A_723] : k7_relat_1(k6_relat_1(A_722),A_723) = k6_relat_1(k3_xboole_0(A_723,A_722)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_39781])).

tff(c_198,plain,(
    ! [A_52,B_53] :
      ( k5_relat_1(k6_relat_1(A_52),B_53) = k7_relat_1(B_53,A_52)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_204,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_34])).

tff(c_210,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_204])).

tff(c_40098,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40031,c_210])).

tff(c_40117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_40098])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:19:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.74/7.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.74/7.25  
% 14.74/7.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.74/7.25  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 14.74/7.25  
% 14.74/7.25  %Foreground sorts:
% 14.74/7.25  
% 14.74/7.25  
% 14.74/7.25  %Background operators:
% 14.74/7.25  
% 14.74/7.25  
% 14.74/7.25  %Foreground operators:
% 14.74/7.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 14.74/7.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.74/7.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.74/7.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.74/7.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.74/7.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.74/7.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.74/7.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.74/7.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.74/7.25  tff('#skF_2', type, '#skF_2': $i).
% 14.74/7.25  tff('#skF_1', type, '#skF_1': $i).
% 14.74/7.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.74/7.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.74/7.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.74/7.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.74/7.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.74/7.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.74/7.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.74/7.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.74/7.25  
% 14.74/7.26  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.74/7.26  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.74/7.26  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 14.74/7.26  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 14.74/7.26  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 14.74/7.26  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 14.74/7.26  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 14.74/7.26  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 14.74/7.26  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 14.74/7.26  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 14.74/7.26  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 14.74/7.26  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 14.74/7.26  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 14.74/7.26  tff(f_80, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 14.74/7.26  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.74/7.26  tff(c_98, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.74/7.26  tff(c_113, plain, (![B_44, A_45]: (k1_setfam_1(k2_tarski(B_44, A_45))=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_4, c_98])).
% 14.74/7.26  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.74/7.26  tff(c_119, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_113, c_10])).
% 14.74/7.26  tff(c_136, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_113, c_10])).
% 14.74/7.26  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.74/7.26  tff(c_157, plain, (![B_46, A_47]: (r1_tarski(k3_xboole_0(B_46, A_47), A_47))), inference(superposition, [status(thm), theory('equality')], [c_136, c_2])).
% 14.74/7.26  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.74/7.26  tff(c_222, plain, (![B_57, A_58]: (k5_relat_1(B_57, k6_relat_1(A_58))=k8_relat_1(A_58, B_57) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.74/7.26  tff(c_30, plain, (![A_27, B_28]: (k5_relat_1(k6_relat_1(A_27), B_28)=k7_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.74/7.26  tff(c_229, plain, (![A_58, A_27]: (k8_relat_1(A_58, k6_relat_1(A_27))=k7_relat_1(k6_relat_1(A_58), A_27) | ~v1_relat_1(k6_relat_1(A_58)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_222, c_30])).
% 14.74/7.26  tff(c_242, plain, (![A_58, A_27]: (k8_relat_1(A_58, k6_relat_1(A_27))=k7_relat_1(k6_relat_1(A_58), A_27))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_229])).
% 14.74/7.26  tff(c_348, plain, (![B_71, A_72]: (k3_xboole_0(B_71, k2_zfmisc_1(k1_relat_1(B_71), A_72))=k8_relat_1(A_72, B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.74/7.26  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.74/7.26  tff(c_392, plain, (![A_77, B_78]: (v1_relat_1(k8_relat_1(A_77, B_78)) | ~v1_relat_1(B_78) | ~v1_relat_1(B_78))), inference(superposition, [status(thm), theory('equality')], [c_348, c_14])).
% 14.74/7.26  tff(c_395, plain, (![A_58, A_27]: (v1_relat_1(k7_relat_1(k6_relat_1(A_58), A_27)) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_242, c_392])).
% 14.74/7.26  tff(c_397, plain, (![A_58, A_27]: (v1_relat_1(k7_relat_1(k6_relat_1(A_58), A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_395])).
% 14.74/7.26  tff(c_22, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.74/7.26  tff(c_259, plain, (![B_61, A_62]: (k3_xboole_0(k1_relat_1(B_61), A_62)=k1_relat_1(k7_relat_1(B_61, A_62)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.74/7.26  tff(c_330, plain, (![B_69, A_70]: (r1_tarski(k1_relat_1(k7_relat_1(B_69, A_70)), k1_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_259, c_2])).
% 14.74/7.26  tff(c_32, plain, (![B_30, A_29]: (k7_relat_1(B_30, A_29)=B_30 | ~r1_tarski(k1_relat_1(B_30), A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.74/7.26  tff(c_3327, plain, (![B_171, A_172]: (k7_relat_1(k7_relat_1(B_171, A_172), k1_relat_1(B_171))=k7_relat_1(B_171, A_172) | ~v1_relat_1(k7_relat_1(B_171, A_172)) | ~v1_relat_1(B_171))), inference(resolution, [status(thm)], [c_330, c_32])).
% 14.74/7.26  tff(c_3396, plain, (![A_22, A_172]: (k7_relat_1(k7_relat_1(k6_relat_1(A_22), A_172), A_22)=k7_relat_1(k6_relat_1(A_22), A_172) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_22), A_172)) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3327])).
% 14.74/7.26  tff(c_3889, plain, (![A_181, A_182]: (k7_relat_1(k7_relat_1(k6_relat_1(A_181), A_182), A_181)=k7_relat_1(k6_relat_1(A_181), A_182))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_397, c_3396])).
% 14.74/7.26  tff(c_16, plain, (![C_17, A_15, B_16]: (k7_relat_1(k7_relat_1(C_17, A_15), B_16)=k7_relat_1(C_17, k3_xboole_0(A_15, B_16)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.74/7.26  tff(c_3918, plain, (![A_181, A_182]: (k7_relat_1(k6_relat_1(A_181), k3_xboole_0(A_182, A_181))=k7_relat_1(k6_relat_1(A_181), A_182) | ~v1_relat_1(k6_relat_1(A_181)))), inference(superposition, [status(thm), theory('equality')], [c_3889, c_16])).
% 14.74/7.26  tff(c_39571, plain, (![A_722, A_723]: (k7_relat_1(k6_relat_1(A_722), k3_xboole_0(A_723, A_722))=k7_relat_1(k6_relat_1(A_722), A_723))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3918])).
% 14.74/7.26  tff(c_24, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.74/7.26  tff(c_431, plain, (![B_83, A_84]: (k5_relat_1(B_83, k6_relat_1(A_84))=B_83 | ~r1_tarski(k2_relat_1(B_83), A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.74/7.26  tff(c_434, plain, (![A_22, A_84]: (k5_relat_1(k6_relat_1(A_22), k6_relat_1(A_84))=k6_relat_1(A_22) | ~r1_tarski(A_22, A_84) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_431])).
% 14.74/7.26  tff(c_1673, plain, (![A_128, A_129]: (k5_relat_1(k6_relat_1(A_128), k6_relat_1(A_129))=k6_relat_1(A_128) | ~r1_tarski(A_128, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_434])).
% 14.74/7.26  tff(c_1682, plain, (![A_129, A_128]: (k7_relat_1(k6_relat_1(A_129), A_128)=k6_relat_1(A_128) | ~v1_relat_1(k6_relat_1(A_129)) | ~r1_tarski(A_128, A_129))), inference(superposition, [status(thm), theory('equality')], [c_1673, c_30])).
% 14.74/7.26  tff(c_1701, plain, (![A_129, A_128]: (k7_relat_1(k6_relat_1(A_129), A_128)=k6_relat_1(A_128) | ~r1_tarski(A_128, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1682])).
% 14.74/7.26  tff(c_39781, plain, (![A_722, A_723]: (k7_relat_1(k6_relat_1(A_722), A_723)=k6_relat_1(k3_xboole_0(A_723, A_722)) | ~r1_tarski(k3_xboole_0(A_723, A_722), A_722))), inference(superposition, [status(thm), theory('equality')], [c_39571, c_1701])).
% 14.74/7.26  tff(c_40031, plain, (![A_722, A_723]: (k7_relat_1(k6_relat_1(A_722), A_723)=k6_relat_1(k3_xboole_0(A_723, A_722)))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_39781])).
% 14.74/7.26  tff(c_198, plain, (![A_52, B_53]: (k5_relat_1(k6_relat_1(A_52), B_53)=k7_relat_1(B_53, A_52) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.74/7.26  tff(c_34, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.74/7.26  tff(c_204, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_198, c_34])).
% 14.74/7.26  tff(c_210, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_204])).
% 14.74/7.26  tff(c_40098, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40031, c_210])).
% 14.74/7.26  tff(c_40117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_40098])).
% 14.74/7.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.74/7.26  
% 14.74/7.26  Inference rules
% 14.74/7.26  ----------------------
% 14.74/7.26  #Ref     : 0
% 14.74/7.26  #Sup     : 10248
% 14.74/7.26  #Fact    : 0
% 14.74/7.26  #Define  : 0
% 14.74/7.26  #Split   : 2
% 14.74/7.26  #Chain   : 0
% 14.74/7.26  #Close   : 0
% 14.74/7.26  
% 14.74/7.26  Ordering : KBO
% 14.74/7.26  
% 14.74/7.26  Simplification rules
% 14.74/7.26  ----------------------
% 14.74/7.26  #Subsume      : 1765
% 14.74/7.26  #Demod        : 8968
% 14.74/7.26  #Tautology    : 2973
% 14.74/7.26  #SimpNegUnit  : 0
% 14.74/7.26  #BackRed      : 58
% 14.74/7.26  
% 14.74/7.26  #Partial instantiations: 0
% 14.74/7.26  #Strategies tried      : 1
% 14.74/7.26  
% 14.74/7.26  Timing (in seconds)
% 14.74/7.26  ----------------------
% 14.74/7.27  Preprocessing        : 0.30
% 14.74/7.27  Parsing              : 0.16
% 14.74/7.27  CNF conversion       : 0.02
% 14.74/7.27  Main loop            : 6.19
% 14.74/7.27  Inferencing          : 1.13
% 14.74/7.27  Reduction            : 3.03
% 14.74/7.27  Demodulation         : 2.67
% 14.74/7.27  BG Simplification    : 0.17
% 14.74/7.27  Subsumption          : 1.52
% 14.74/7.27  Abstraction          : 0.25
% 14.74/7.27  MUC search           : 0.00
% 14.74/7.27  Cooper               : 0.00
% 14.74/7.27  Total                : 6.52
% 14.74/7.27  Index Insertion      : 0.00
% 14.74/7.27  Index Deletion       : 0.00
% 14.74/7.27  Index Matching       : 0.00
% 14.74/7.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
