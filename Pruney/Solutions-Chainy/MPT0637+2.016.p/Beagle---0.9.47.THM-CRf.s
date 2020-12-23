%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:26 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 171 expanded)
%              Number of leaves         :   36 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 244 expanded)
%              Number of equality atoms :   46 (  95 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_63,B_64] : k1_setfam_1(k2_tarski(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    ! [B_65,A_66] : k1_setfam_1(k2_tarski(B_65,A_66)) = k3_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_107])).

tff(c_20,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [B_67,A_68] : k3_xboole_0(B_67,A_68) = k3_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_20])).

tff(c_160,plain,(
    ! [B_67,A_68] : r1_tarski(k3_xboole_0(B_67,A_68),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_2])).

tff(c_24,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [A_52,B_53] :
      ( k5_relat_1(k6_relat_1(A_52),B_53) = k7_relat_1(B_53,A_52)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_338,plain,(
    ! [B_86,A_87] :
      ( k5_relat_1(B_86,k6_relat_1(A_87)) = k8_relat_1(A_87,B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_370,plain,(
    ! [A_87,A_52] :
      ( k8_relat_1(A_87,k6_relat_1(A_52)) = k7_relat_1(k6_relat_1(A_87),A_52)
      | ~ v1_relat_1(k6_relat_1(A_52))
      | ~ v1_relat_1(k6_relat_1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_338])).

tff(c_394,plain,(
    ! [A_87,A_52] : k8_relat_1(A_87,k6_relat_1(A_52)) = k7_relat_1(k6_relat_1(A_87),A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_370])).

tff(c_32,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_561,plain,(
    ! [B_105,A_106] :
      ( k5_relat_1(B_105,k6_relat_1(A_106)) = B_105
      | ~ r1_tarski(k2_relat_1(B_105),A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_568,plain,(
    ! [A_45,A_106] :
      ( k5_relat_1(k6_relat_1(A_45),k6_relat_1(A_106)) = k6_relat_1(A_45)
      | ~ r1_tarski(A_45,A_106)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_561])).

tff(c_713,plain,(
    ! [A_114,A_115] :
      ( k5_relat_1(k6_relat_1(A_114),k6_relat_1(A_115)) = k6_relat_1(A_114)
      | ~ r1_tarski(A_114,A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_568])).

tff(c_26,plain,(
    ! [B_40,A_39] :
      ( k5_relat_1(B_40,k6_relat_1(A_39)) = k8_relat_1(A_39,B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_719,plain,(
    ! [A_115,A_114] :
      ( k8_relat_1(A_115,k6_relat_1(A_114)) = k6_relat_1(A_114)
      | ~ v1_relat_1(k6_relat_1(A_114))
      | ~ r1_tarski(A_114,A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_26])).

tff(c_765,plain,(
    ! [A_115,A_114] :
      ( k7_relat_1(k6_relat_1(A_115),A_114) = k6_relat_1(A_114)
      | ~ r1_tarski(A_114,A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_394,c_719])).

tff(c_419,plain,(
    ! [A_91,A_92] : k8_relat_1(A_91,k6_relat_1(A_92)) = k7_relat_1(k6_relat_1(A_91),A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_370])).

tff(c_22,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k5_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_348,plain,(
    ! [A_87,B_86] :
      ( v1_relat_1(k8_relat_1(A_87,B_86))
      | ~ v1_relat_1(k6_relat_1(A_87))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_22])).

tff(c_385,plain,(
    ! [A_87,B_86] :
      ( v1_relat_1(k8_relat_1(A_87,B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_348])).

tff(c_429,plain,(
    ! [A_91,A_92] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_91),A_92))
      | ~ v1_relat_1(k6_relat_1(A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_385])).

tff(c_439,plain,(
    ! [A_91,A_92] : v1_relat_1(k7_relat_1(k6_relat_1(A_91),A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_429])).

tff(c_30,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_446,plain,(
    ! [B_95,A_96] :
      ( k3_xboole_0(k1_relat_1(B_95),A_96) = k1_relat_1(k7_relat_1(B_95,A_96))
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_475,plain,(
    ! [A_45,A_96] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_45),A_96)) = k3_xboole_0(A_45,A_96)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_446])).

tff(c_479,plain,(
    ! [A_45,A_96] : k1_relat_1(k7_relat_1(k6_relat_1(A_45),A_96)) = k3_xboole_0(A_45,A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_475])).

tff(c_34,plain,(
    ! [A_46] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_46)),A_46) = A_46
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1243,plain,(
    ! [A_135,B_136,C_137] :
      ( k8_relat_1(A_135,k5_relat_1(B_136,C_137)) = k5_relat_1(B_136,k8_relat_1(A_135,C_137))
      | ~ v1_relat_1(C_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1266,plain,(
    ! [B_40,A_135,A_39] :
      ( k5_relat_1(B_40,k8_relat_1(A_135,k6_relat_1(A_39))) = k8_relat_1(A_135,k8_relat_1(A_39,B_40))
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1243])).

tff(c_3798,plain,(
    ! [B_199,A_200,A_201] :
      ( k5_relat_1(B_199,k7_relat_1(k6_relat_1(A_200),A_201)) = k8_relat_1(A_200,k8_relat_1(A_201,B_199))
      | ~ v1_relat_1(B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_394,c_1266])).

tff(c_3843,plain,(
    ! [A_200,A_201] :
      ( k8_relat_1(A_200,k8_relat_1(A_201,k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_200),A_201))))) = k7_relat_1(k6_relat_1(A_200),A_201)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_200),A_201))))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_200),A_201)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3798])).

tff(c_10198,plain,(
    ! [A_304,A_305] : k8_relat_1(A_304,k7_relat_1(k6_relat_1(A_305),k3_xboole_0(A_304,A_305))) = k7_relat_1(k6_relat_1(A_304),A_305) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_24,c_479,c_394,c_3843])).

tff(c_10313,plain,(
    ! [A_304,A_115] :
      ( k8_relat_1(A_304,k6_relat_1(k3_xboole_0(A_304,A_115))) = k7_relat_1(k6_relat_1(A_304),A_115)
      | ~ r1_tarski(k3_xboole_0(A_304,A_115),A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_10198])).

tff(c_10356,plain,(
    ! [A_306,A_307] : k7_relat_1(k6_relat_1(A_306),k3_xboole_0(A_306,A_307)) = k7_relat_1(k6_relat_1(A_306),A_307) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_394,c_10313])).

tff(c_10421,plain,(
    ! [A_306,A_307] :
      ( k7_relat_1(k6_relat_1(A_306),A_307) = k6_relat_1(k3_xboole_0(A_306,A_307))
      | ~ r1_tarski(k3_xboole_0(A_306,A_307),A_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10356,c_765])).

tff(c_10558,plain,(
    ! [A_306,A_307] : k7_relat_1(k6_relat_1(A_306),A_307) = k6_relat_1(k3_xboole_0(A_306,A_307)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10421])).

tff(c_272,plain,(
    ! [A_81,B_82] :
      ( k5_relat_1(k6_relat_1(A_81),B_82) = k7_relat_1(B_82,A_81)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_293,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_44])).

tff(c_315,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_293])).

tff(c_10607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10558,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.22/2.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.22/2.69  
% 7.22/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.22/2.69  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.22/2.69  
% 7.22/2.69  %Foreground sorts:
% 7.22/2.69  
% 7.22/2.69  
% 7.22/2.69  %Background operators:
% 7.22/2.69  
% 7.22/2.69  
% 7.22/2.69  %Foreground operators:
% 7.22/2.69  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.22/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.22/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.22/2.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.22/2.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.22/2.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.22/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.22/2.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.22/2.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.22/2.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.22/2.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.22/2.69  tff('#skF_2', type, '#skF_2': $i).
% 7.22/2.69  tff('#skF_1', type, '#skF_1': $i).
% 7.22/2.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.22/2.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.22/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.22/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.22/2.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.22/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.22/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.22/2.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.22/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.22/2.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.22/2.69  
% 7.22/2.71  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.22/2.71  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.22/2.71  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.22/2.71  tff(f_53, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.22/2.71  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 7.22/2.71  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 7.22/2.71  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.22/2.71  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 7.22/2.71  tff(f_51, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.22/2.71  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 7.22/2.71  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 7.22/2.71  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 7.22/2.71  tff(f_93, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 7.22/2.71  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.22/2.71  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.71  tff(c_107, plain, (![A_63, B_64]: (k1_setfam_1(k2_tarski(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.71  tff(c_122, plain, (![B_65, A_66]: (k1_setfam_1(k2_tarski(B_65, A_66))=k3_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_6, c_107])).
% 7.22/2.71  tff(c_20, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.71  tff(c_145, plain, (![B_67, A_68]: (k3_xboole_0(B_67, A_68)=k3_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_122, c_20])).
% 7.22/2.71  tff(c_160, plain, (![B_67, A_68]: (r1_tarski(k3_xboole_0(B_67, A_68), A_68))), inference(superposition, [status(thm), theory('equality')], [c_145, c_2])).
% 7.22/2.71  tff(c_24, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.22/2.71  tff(c_42, plain, (![A_52, B_53]: (k5_relat_1(k6_relat_1(A_52), B_53)=k7_relat_1(B_53, A_52) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.22/2.71  tff(c_338, plain, (![B_86, A_87]: (k5_relat_1(B_86, k6_relat_1(A_87))=k8_relat_1(A_87, B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.22/2.71  tff(c_370, plain, (![A_87, A_52]: (k8_relat_1(A_87, k6_relat_1(A_52))=k7_relat_1(k6_relat_1(A_87), A_52) | ~v1_relat_1(k6_relat_1(A_52)) | ~v1_relat_1(k6_relat_1(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_338])).
% 7.22/2.71  tff(c_394, plain, (![A_87, A_52]: (k8_relat_1(A_87, k6_relat_1(A_52))=k7_relat_1(k6_relat_1(A_87), A_52))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_370])).
% 7.22/2.71  tff(c_32, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.22/2.71  tff(c_561, plain, (![B_105, A_106]: (k5_relat_1(B_105, k6_relat_1(A_106))=B_105 | ~r1_tarski(k2_relat_1(B_105), A_106) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.22/2.71  tff(c_568, plain, (![A_45, A_106]: (k5_relat_1(k6_relat_1(A_45), k6_relat_1(A_106))=k6_relat_1(A_45) | ~r1_tarski(A_45, A_106) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_561])).
% 7.22/2.71  tff(c_713, plain, (![A_114, A_115]: (k5_relat_1(k6_relat_1(A_114), k6_relat_1(A_115))=k6_relat_1(A_114) | ~r1_tarski(A_114, A_115))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_568])).
% 7.22/2.71  tff(c_26, plain, (![B_40, A_39]: (k5_relat_1(B_40, k6_relat_1(A_39))=k8_relat_1(A_39, B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.22/2.71  tff(c_719, plain, (![A_115, A_114]: (k8_relat_1(A_115, k6_relat_1(A_114))=k6_relat_1(A_114) | ~v1_relat_1(k6_relat_1(A_114)) | ~r1_tarski(A_114, A_115))), inference(superposition, [status(thm), theory('equality')], [c_713, c_26])).
% 7.22/2.71  tff(c_765, plain, (![A_115, A_114]: (k7_relat_1(k6_relat_1(A_115), A_114)=k6_relat_1(A_114) | ~r1_tarski(A_114, A_115))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_394, c_719])).
% 7.22/2.71  tff(c_419, plain, (![A_91, A_92]: (k8_relat_1(A_91, k6_relat_1(A_92))=k7_relat_1(k6_relat_1(A_91), A_92))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_370])).
% 7.22/2.71  tff(c_22, plain, (![A_36, B_37]: (v1_relat_1(k5_relat_1(A_36, B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.22/2.71  tff(c_348, plain, (![A_87, B_86]: (v1_relat_1(k8_relat_1(A_87, B_86)) | ~v1_relat_1(k6_relat_1(A_87)) | ~v1_relat_1(B_86) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_338, c_22])).
% 7.22/2.71  tff(c_385, plain, (![A_87, B_86]: (v1_relat_1(k8_relat_1(A_87, B_86)) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_348])).
% 7.22/2.71  tff(c_429, plain, (![A_91, A_92]: (v1_relat_1(k7_relat_1(k6_relat_1(A_91), A_92)) | ~v1_relat_1(k6_relat_1(A_92)))), inference(superposition, [status(thm), theory('equality')], [c_419, c_385])).
% 7.22/2.71  tff(c_439, plain, (![A_91, A_92]: (v1_relat_1(k7_relat_1(k6_relat_1(A_91), A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_429])).
% 7.22/2.71  tff(c_30, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.22/2.71  tff(c_446, plain, (![B_95, A_96]: (k3_xboole_0(k1_relat_1(B_95), A_96)=k1_relat_1(k7_relat_1(B_95, A_96)) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.22/2.71  tff(c_475, plain, (![A_45, A_96]: (k1_relat_1(k7_relat_1(k6_relat_1(A_45), A_96))=k3_xboole_0(A_45, A_96) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_446])).
% 7.22/2.71  tff(c_479, plain, (![A_45, A_96]: (k1_relat_1(k7_relat_1(k6_relat_1(A_45), A_96))=k3_xboole_0(A_45, A_96))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_475])).
% 7.22/2.71  tff(c_34, plain, (![A_46]: (k5_relat_1(k6_relat_1(k1_relat_1(A_46)), A_46)=A_46 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.22/2.71  tff(c_1243, plain, (![A_135, B_136, C_137]: (k8_relat_1(A_135, k5_relat_1(B_136, C_137))=k5_relat_1(B_136, k8_relat_1(A_135, C_137)) | ~v1_relat_1(C_137) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.22/2.71  tff(c_1266, plain, (![B_40, A_135, A_39]: (k5_relat_1(B_40, k8_relat_1(A_135, k6_relat_1(A_39)))=k8_relat_1(A_135, k8_relat_1(A_39, B_40)) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(B_40) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1243])).
% 7.22/2.71  tff(c_3798, plain, (![B_199, A_200, A_201]: (k5_relat_1(B_199, k7_relat_1(k6_relat_1(A_200), A_201))=k8_relat_1(A_200, k8_relat_1(A_201, B_199)) | ~v1_relat_1(B_199))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_394, c_1266])).
% 7.22/2.71  tff(c_3843, plain, (![A_200, A_201]: (k8_relat_1(A_200, k8_relat_1(A_201, k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_200), A_201)))))=k7_relat_1(k6_relat_1(A_200), A_201) | ~v1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_200), A_201)))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_200), A_201)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3798])).
% 7.22/2.71  tff(c_10198, plain, (![A_304, A_305]: (k8_relat_1(A_304, k7_relat_1(k6_relat_1(A_305), k3_xboole_0(A_304, A_305)))=k7_relat_1(k6_relat_1(A_304), A_305))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_24, c_479, c_394, c_3843])).
% 7.22/2.71  tff(c_10313, plain, (![A_304, A_115]: (k8_relat_1(A_304, k6_relat_1(k3_xboole_0(A_304, A_115)))=k7_relat_1(k6_relat_1(A_304), A_115) | ~r1_tarski(k3_xboole_0(A_304, A_115), A_115))), inference(superposition, [status(thm), theory('equality')], [c_765, c_10198])).
% 7.22/2.71  tff(c_10356, plain, (![A_306, A_307]: (k7_relat_1(k6_relat_1(A_306), k3_xboole_0(A_306, A_307))=k7_relat_1(k6_relat_1(A_306), A_307))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_394, c_10313])).
% 7.22/2.71  tff(c_10421, plain, (![A_306, A_307]: (k7_relat_1(k6_relat_1(A_306), A_307)=k6_relat_1(k3_xboole_0(A_306, A_307)) | ~r1_tarski(k3_xboole_0(A_306, A_307), A_306))), inference(superposition, [status(thm), theory('equality')], [c_10356, c_765])).
% 7.22/2.71  tff(c_10558, plain, (![A_306, A_307]: (k7_relat_1(k6_relat_1(A_306), A_307)=k6_relat_1(k3_xboole_0(A_306, A_307)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10421])).
% 7.22/2.71  tff(c_272, plain, (![A_81, B_82]: (k5_relat_1(k6_relat_1(A_81), B_82)=k7_relat_1(B_82, A_81) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.22/2.71  tff(c_44, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.22/2.71  tff(c_293, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_44])).
% 7.22/2.71  tff(c_315, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_293])).
% 7.22/2.71  tff(c_10607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10558, c_315])).
% 7.22/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.22/2.71  
% 7.22/2.71  Inference rules
% 7.22/2.71  ----------------------
% 7.22/2.71  #Ref     : 0
% 7.22/2.71  #Sup     : 2651
% 7.22/2.71  #Fact    : 0
% 7.22/2.71  #Define  : 0
% 7.22/2.71  #Split   : 1
% 7.22/2.71  #Chain   : 0
% 7.22/2.71  #Close   : 0
% 7.22/2.71  
% 7.22/2.71  Ordering : KBO
% 7.22/2.71  
% 7.22/2.71  Simplification rules
% 7.22/2.71  ----------------------
% 7.22/2.71  #Subsume      : 358
% 7.22/2.71  #Demod        : 2692
% 7.22/2.71  #Tautology    : 1158
% 7.22/2.71  #SimpNegUnit  : 0
% 7.22/2.71  #BackRed      : 26
% 7.22/2.71  
% 7.22/2.71  #Partial instantiations: 0
% 7.22/2.71  #Strategies tried      : 1
% 7.22/2.71  
% 7.22/2.71  Timing (in seconds)
% 7.22/2.71  ----------------------
% 7.22/2.71  Preprocessing        : 0.34
% 7.22/2.71  Parsing              : 0.19
% 7.22/2.71  CNF conversion       : 0.02
% 7.22/2.71  Main loop            : 1.56
% 7.22/2.71  Inferencing          : 0.43
% 7.22/2.71  Reduction            : 0.76
% 7.22/2.71  Demodulation         : 0.65
% 7.22/2.71  BG Simplification    : 0.06
% 7.22/2.71  Subsumption          : 0.24
% 7.22/2.71  Abstraction          : 0.08
% 7.22/2.71  MUC search           : 0.00
% 7.22/2.71  Cooper               : 0.00
% 7.22/2.71  Total                : 1.93
% 7.22/2.71  Index Insertion      : 0.00
% 7.22/2.71  Index Deletion       : 0.00
% 7.22/2.71  Index Matching       : 0.00
% 7.22/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
