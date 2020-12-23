%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:45 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 8.07s
% Verified   : 
% Statistics : Number of formulae       :  146 (3781 expanded)
%              Number of leaves         :   41 (1332 expanded)
%              Depth                    :   38
%              Number of atoms          :  249 (7188 expanded)
%              Number of equality atoms :   68 (2080 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_63,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_128,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | k4_xboole_0(A_65,B_66) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_135,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128,c_54])).

tff(c_58,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_178,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_187,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_190,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_187])).

tff(c_34,plain,(
    ! [A_31,B_32] :
      ( v1_relat_1(k7_relat_1(A_31,B_32))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_312,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_tarski(A_91,C_92)
      | ~ r1_tarski(B_93,C_92)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_347,plain,(
    ! [A_95] :
      ( r1_tarski(A_95,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_95,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_56,c_312])).

tff(c_28,plain,(
    ! [B_29,A_28] :
      ( v4_relat_1(B_29,A_28)
      | ~ r1_tarski(k1_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_636,plain,(
    ! [B_117] :
      ( v4_relat_1(B_117,k1_relat_1('#skF_2'))
      | ~ v1_relat_1(B_117)
      | ~ r1_tarski(k1_relat_1(B_117),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_347,c_28])).

tff(c_44,plain,(
    ! [B_44,A_43] :
      ( k7_relat_1(B_44,A_43) = B_44
      | ~ v4_relat_1(B_44,A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1391,plain,(
    ! [B_170] :
      ( k7_relat_1(B_170,k1_relat_1('#skF_2')) = B_170
      | ~ v1_relat_1(B_170)
      | ~ r1_tarski(k1_relat_1(B_170),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_636,c_44])).

tff(c_1408,plain,(
    ! [B_170] :
      ( k7_relat_1(B_170,k1_relat_1('#skF_2')) = B_170
      | ~ v1_relat_1(B_170)
      | k4_xboole_0(k1_relat_1(B_170),'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1391])).

tff(c_1598,plain,(
    ! [A_174,B_175] :
      ( k7_relat_1(A_174,k1_relat_1(k7_relat_1(B_175,k1_relat_1(A_174)))) = k7_relat_1(A_174,k1_relat_1(B_175))
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1672,plain,(
    ! [A_45,B_175] :
      ( k7_relat_1(k6_relat_1(A_45),k1_relat_1(k7_relat_1(B_175,A_45))) = k7_relat_1(k6_relat_1(A_45),k1_relat_1(B_175))
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1598])).

tff(c_3319,plain,(
    ! [A_244,B_245] :
      ( k7_relat_1(k6_relat_1(A_244),k1_relat_1(k7_relat_1(B_245,A_244))) = k7_relat_1(k6_relat_1(A_244),k1_relat_1(B_245))
      | ~ v1_relat_1(B_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1672])).

tff(c_3382,plain,(
    ! [A_244,B_245] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_244),k1_relat_1(B_245)))
      | ~ v1_relat_1(k6_relat_1(A_244))
      | ~ v1_relat_1(B_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3319,c_34])).

tff(c_3474,plain,(
    ! [A_246,B_247] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_246),k1_relat_1(B_247)))
      | ~ v1_relat_1(B_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3382])).

tff(c_3513,plain,(
    ! [A_246,A_45] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_246),A_45))
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3474])).

tff(c_3526,plain,(
    ! [A_246,A_45] : v1_relat_1(k7_relat_1(k6_relat_1(A_246),A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3513])).

tff(c_48,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_137,plain,(
    ! [A_67] :
      ( k10_relat_1(A_67,k2_relat_1(A_67)) = k1_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_146,plain,(
    ! [A_45] :
      ( k10_relat_1(k6_relat_1(A_45),A_45) = k1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_137])).

tff(c_150,plain,(
    ! [A_45] : k10_relat_1(k6_relat_1(A_45),A_45) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46,c_146])).

tff(c_259,plain,(
    ! [B_87,A_88] :
      ( v4_relat_1(B_87,A_88)
      | ~ r1_tarski(k1_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_272,plain,(
    ! [A_45,A_88] :
      ( v4_relat_1(k6_relat_1(A_45),A_88)
      | ~ r1_tarski(A_45,A_88)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_259])).

tff(c_363,plain,(
    ! [A_96,A_97] :
      ( v4_relat_1(k6_relat_1(A_96),A_97)
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_272])).

tff(c_369,plain,(
    ! [A_96,A_97] :
      ( k7_relat_1(k6_relat_1(A_96),A_97) = k6_relat_1(A_96)
      | ~ v1_relat_1(k6_relat_1(A_96))
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(resolution,[status(thm)],[c_363,c_44])).

tff(c_373,plain,(
    ! [A_96,A_97] :
      ( k7_relat_1(k6_relat_1(A_96),A_97) = k6_relat_1(A_96)
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_369])).

tff(c_761,plain,(
    ! [A_127,C_128,B_129] :
      ( k3_xboole_0(A_127,k10_relat_1(C_128,B_129)) = k10_relat_1(k7_relat_1(C_128,A_127),B_129)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_777,plain,(
    ! [A_45,A_127] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_45),A_127),A_45) = k3_xboole_0(A_127,A_45)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_761])).

tff(c_789,plain,(
    ! [A_130,A_131] : k10_relat_1(k7_relat_1(k6_relat_1(A_130),A_131),A_130) = k3_xboole_0(A_131,A_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_777])).

tff(c_801,plain,(
    ! [A_97,A_96] :
      ( k3_xboole_0(A_97,A_96) = k10_relat_1(k6_relat_1(A_96),A_96)
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_789])).

tff(c_815,plain,(
    ! [A_132,A_133] :
      ( k3_xboole_0(A_132,A_133) = A_133
      | ~ r1_tarski(A_133,A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_801])).

tff(c_838,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_815])).

tff(c_50,plain,(
    ! [B_47,A_46] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_47,A_46)),A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4143,plain,(
    ! [A_266,B_267] :
      ( k3_xboole_0(A_266,k1_relat_1(k7_relat_1(B_267,A_266))) = k1_relat_1(k7_relat_1(B_267,A_266))
      | ~ v1_relat_1(B_267) ) ),
    inference(resolution,[status(thm)],[c_50,c_815])).

tff(c_4202,plain,(
    ! [A_97,A_96] :
      ( k3_xboole_0(A_97,k1_relat_1(k6_relat_1(A_96))) = k1_relat_1(k7_relat_1(k6_relat_1(A_96),A_97))
      | ~ v1_relat_1(k6_relat_1(A_96))
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_4143])).

tff(c_4231,plain,(
    ! [A_268,A_269] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_268),A_269)) = k3_xboole_0(A_269,A_268)
      | ~ r1_tarski(A_268,A_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46,c_4202])).

tff(c_282,plain,(
    ! [B_87] :
      ( v4_relat_1(B_87,k1_relat_1(B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_8,c_259])).

tff(c_4314,plain,(
    ! [A_268,A_269] :
      ( v4_relat_1(k7_relat_1(k6_relat_1(A_268),A_269),k3_xboole_0(A_269,A_268))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_268),A_269))
      | ~ r1_tarski(A_268,A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4231,c_282])).

tff(c_7772,plain,(
    ! [A_305,A_306] :
      ( v4_relat_1(k7_relat_1(k6_relat_1(A_305),A_306),k3_xboole_0(A_306,A_305))
      | ~ r1_tarski(A_305,A_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3526,c_4314])).

tff(c_7826,plain,
    ( v4_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')),'#skF_1')
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_7772])).

tff(c_7860,plain,(
    v4_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7826])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_relat_1(B_29),A_28)
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_718,plain,(
    ! [A_124,A_125] :
      ( r1_tarski(A_124,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_124,A_125)
      | ~ r1_tarski(A_125,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_347,c_16])).

tff(c_732,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_relat_1(B_29),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_28,'#skF_1')
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_30,c_718])).

tff(c_7868,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7860,c_732])).

tff(c_7889,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3526,c_8,c_7868])).

tff(c_7928,plain,
    ( v4_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1('#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7889,c_28])).

tff(c_7975,plain,(
    v4_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3526,c_7928])).

tff(c_8097,plain,
    ( v4_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | k4_xboole_0(k1_relat_1(k6_relat_1('#skF_1')),'#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1408,c_7975])).

tff(c_8117,plain,(
    v4_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_46,c_32,c_8097])).

tff(c_8144,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k6_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8117,c_44])).

tff(c_8158,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8144])).

tff(c_1631,plain,(
    ! [A_174,B_175] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_174,k1_relat_1(B_175))),k1_relat_1(k7_relat_1(B_175,k1_relat_1(A_174))))
      | ~ v1_relat_1(A_174)
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(A_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1598,c_50])).

tff(c_8565,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1('#skF_1')),k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(k6_relat_1('#skF_1')))))
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8158,c_1631])).

tff(c_8679,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_58,c_32,c_46,c_46,c_8565])).

tff(c_198,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_74,A_75)),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_204,plain,(
    ! [B_74,A_75] :
      ( k1_relat_1(k7_relat_1(B_74,A_75)) = A_75
      | ~ r1_tarski(A_75,k1_relat_1(k7_relat_1(B_74,A_75)))
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_198,c_4])).

tff(c_8758,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8679,c_204])).

tff(c_8793,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8758])).

tff(c_8944,plain,
    ( v4_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8793,c_282])).

tff(c_9099,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_8944])).

tff(c_9102,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_9099])).

tff(c_9106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9102])).

tff(c_9108,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_8944])).

tff(c_9107,plain,(
    v4_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_8944])).

tff(c_9307,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_9107,c_44])).

tff(c_9313,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9108,c_9307])).

tff(c_4602,plain,(
    ! [A_274,B_275] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_274,k1_relat_1(B_275))),k1_relat_1(k7_relat_1(B_275,k1_relat_1(A_274))))
      | ~ v1_relat_1(A_274)
      | ~ v1_relat_1(B_275)
      | ~ v1_relat_1(A_274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1598,c_50])).

tff(c_324,plain,(
    ! [A_91,A_46,B_47] :
      ( r1_tarski(A_91,A_46)
      | ~ r1_tarski(A_91,k1_relat_1(k7_relat_1(B_47,A_46)))
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_50,c_312])).

tff(c_9109,plain,(
    ! [A_312,B_313] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_312,k1_relat_1(B_313))),k1_relat_1(A_312))
      | ~ v1_relat_1(B_313)
      | ~ v1_relat_1(A_312) ) ),
    inference(resolution,[status(thm)],[c_4602,c_324])).

tff(c_9240,plain,(
    ! [A_312,A_45] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_312,A_45)),k1_relat_1(A_312))
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_9109])).

tff(c_9413,plain,(
    ! [A_314,A_315] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_314,A_315)),k1_relat_1(A_314))
      | ~ v1_relat_1(A_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9240])).

tff(c_9466,plain,(
    ! [A_315] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_315)),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8793,c_9413])).

tff(c_10222,plain,(
    ! [A_329] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_329)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9108,c_9466])).

tff(c_1012,plain,(
    ! [A_142,C_143,B_144] :
      ( k9_relat_1(k7_relat_1(A_142,C_143),B_144) = k9_relat_1(A_142,B_144)
      | ~ r1_tarski(B_144,C_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_33] :
      ( k9_relat_1(A_33,k1_relat_1(A_33)) = k2_relat_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1019,plain,(
    ! [A_142,C_143] :
      ( k9_relat_1(A_142,k1_relat_1(k7_relat_1(A_142,C_143))) = k2_relat_1(k7_relat_1(A_142,C_143))
      | ~ v1_relat_1(k7_relat_1(A_142,C_143))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_142,C_143)),C_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_36])).

tff(c_10232,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))) = k2_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_10222,c_1019])).

tff(c_10298,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9108,c_9108,c_9313,c_9313,c_8793,c_9313,c_10232])).

tff(c_38,plain,(
    ! [A_34,C_38,B_37] :
      ( k9_relat_1(k7_relat_1(A_34,C_38),B_37) = k9_relat_1(A_34,B_37)
      | ~ r1_tarski(B_37,C_38)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10736,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10298,c_38])).

tff(c_10743,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8,c_10736])).

tff(c_40,plain,(
    ! [A_39] :
      ( k10_relat_1(A_39,k2_relat_1(A_39)) = k1_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10808,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10743,c_40])).

tff(c_10814,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9108,c_8793,c_10808])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_767,plain,(
    ! [A_127,C_128,B_129] :
      ( k5_xboole_0(A_127,k10_relat_1(k7_relat_1(C_128,A_127),B_129)) = k4_xboole_0(A_127,k10_relat_1(C_128,B_129))
      | ~ v1_relat_1(C_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_14])).

tff(c_10996,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10814,c_767])).

tff(c_11006,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_190,c_10996])).

tff(c_11008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_11006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.61/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/2.69  
% 7.97/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/2.69  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.97/2.69  
% 7.97/2.69  %Foreground sorts:
% 7.97/2.69  
% 7.97/2.69  
% 7.97/2.69  %Background operators:
% 7.97/2.69  
% 7.97/2.69  
% 7.97/2.69  %Foreground operators:
% 7.97/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.97/2.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.97/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.97/2.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.97/2.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.97/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.97/2.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.97/2.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.97/2.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.97/2.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.97/2.69  tff('#skF_2', type, '#skF_2': $i).
% 7.97/2.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.97/2.69  tff('#skF_1', type, '#skF_1': $i).
% 7.97/2.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.97/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/2.69  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.97/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.97/2.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.97/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/2.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.97/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.97/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.97/2.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.97/2.69  
% 8.07/2.71  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.07/2.71  tff(f_114, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 8.07/2.71  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.07/2.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.07/2.71  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.07/2.71  tff(f_67, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 8.07/2.71  tff(f_63, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 8.07/2.71  tff(f_99, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.07/2.71  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.07/2.71  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.07/2.71  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.07/2.71  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 8.07/2.71  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 8.07/2.71  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 8.07/2.71  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 8.07/2.71  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 8.07/2.71  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 8.07/2.71  tff(c_128, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | k4_xboole_0(A_65, B_66)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.07/2.71  tff(c_54, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.07/2.71  tff(c_135, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_128, c_54])).
% 8.07/2.71  tff(c_58, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.07/2.71  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.07/2.71  tff(c_90, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.07/2.71  tff(c_98, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_90])).
% 8.07/2.71  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.07/2.71  tff(c_178, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.07/2.71  tff(c_187, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 8.07/2.71  tff(c_190, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_187])).
% 8.07/2.71  tff(c_34, plain, (![A_31, B_32]: (v1_relat_1(k7_relat_1(A_31, B_32)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.07/2.71  tff(c_32, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.07/2.71  tff(c_46, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.07/2.71  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.07/2.71  tff(c_56, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.07/2.71  tff(c_312, plain, (![A_91, C_92, B_93]: (r1_tarski(A_91, C_92) | ~r1_tarski(B_93, C_92) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.07/2.71  tff(c_347, plain, (![A_95]: (r1_tarski(A_95, k1_relat_1('#skF_2')) | ~r1_tarski(A_95, '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_312])).
% 8.07/2.71  tff(c_28, plain, (![B_29, A_28]: (v4_relat_1(B_29, A_28) | ~r1_tarski(k1_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.07/2.71  tff(c_636, plain, (![B_117]: (v4_relat_1(B_117, k1_relat_1('#skF_2')) | ~v1_relat_1(B_117) | ~r1_tarski(k1_relat_1(B_117), '#skF_1'))), inference(resolution, [status(thm)], [c_347, c_28])).
% 8.07/2.71  tff(c_44, plain, (![B_44, A_43]: (k7_relat_1(B_44, A_43)=B_44 | ~v4_relat_1(B_44, A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.07/2.71  tff(c_1391, plain, (![B_170]: (k7_relat_1(B_170, k1_relat_1('#skF_2'))=B_170 | ~v1_relat_1(B_170) | ~r1_tarski(k1_relat_1(B_170), '#skF_1'))), inference(resolution, [status(thm)], [c_636, c_44])).
% 8.07/2.71  tff(c_1408, plain, (![B_170]: (k7_relat_1(B_170, k1_relat_1('#skF_2'))=B_170 | ~v1_relat_1(B_170) | k4_xboole_0(k1_relat_1(B_170), '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1391])).
% 8.07/2.71  tff(c_1598, plain, (![A_174, B_175]: (k7_relat_1(A_174, k1_relat_1(k7_relat_1(B_175, k1_relat_1(A_174))))=k7_relat_1(A_174, k1_relat_1(B_175)) | ~v1_relat_1(B_175) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.07/2.71  tff(c_1672, plain, (![A_45, B_175]: (k7_relat_1(k6_relat_1(A_45), k1_relat_1(k7_relat_1(B_175, A_45)))=k7_relat_1(k6_relat_1(A_45), k1_relat_1(B_175)) | ~v1_relat_1(B_175) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1598])).
% 8.07/2.71  tff(c_3319, plain, (![A_244, B_245]: (k7_relat_1(k6_relat_1(A_244), k1_relat_1(k7_relat_1(B_245, A_244)))=k7_relat_1(k6_relat_1(A_244), k1_relat_1(B_245)) | ~v1_relat_1(B_245))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1672])).
% 8.07/2.71  tff(c_3382, plain, (![A_244, B_245]: (v1_relat_1(k7_relat_1(k6_relat_1(A_244), k1_relat_1(B_245))) | ~v1_relat_1(k6_relat_1(A_244)) | ~v1_relat_1(B_245))), inference(superposition, [status(thm), theory('equality')], [c_3319, c_34])).
% 8.07/2.71  tff(c_3474, plain, (![A_246, B_247]: (v1_relat_1(k7_relat_1(k6_relat_1(A_246), k1_relat_1(B_247))) | ~v1_relat_1(B_247))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3382])).
% 8.07/2.71  tff(c_3513, plain, (![A_246, A_45]: (v1_relat_1(k7_relat_1(k6_relat_1(A_246), A_45)) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3474])).
% 8.07/2.71  tff(c_3526, plain, (![A_246, A_45]: (v1_relat_1(k7_relat_1(k6_relat_1(A_246), A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3513])).
% 8.07/2.71  tff(c_48, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.07/2.71  tff(c_137, plain, (![A_67]: (k10_relat_1(A_67, k2_relat_1(A_67))=k1_relat_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.07/2.71  tff(c_146, plain, (![A_45]: (k10_relat_1(k6_relat_1(A_45), A_45)=k1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_137])).
% 8.07/2.71  tff(c_150, plain, (![A_45]: (k10_relat_1(k6_relat_1(A_45), A_45)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46, c_146])).
% 8.07/2.71  tff(c_259, plain, (![B_87, A_88]: (v4_relat_1(B_87, A_88) | ~r1_tarski(k1_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.07/2.71  tff(c_272, plain, (![A_45, A_88]: (v4_relat_1(k6_relat_1(A_45), A_88) | ~r1_tarski(A_45, A_88) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_259])).
% 8.07/2.71  tff(c_363, plain, (![A_96, A_97]: (v4_relat_1(k6_relat_1(A_96), A_97) | ~r1_tarski(A_96, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_272])).
% 8.07/2.71  tff(c_369, plain, (![A_96, A_97]: (k7_relat_1(k6_relat_1(A_96), A_97)=k6_relat_1(A_96) | ~v1_relat_1(k6_relat_1(A_96)) | ~r1_tarski(A_96, A_97))), inference(resolution, [status(thm)], [c_363, c_44])).
% 8.07/2.71  tff(c_373, plain, (![A_96, A_97]: (k7_relat_1(k6_relat_1(A_96), A_97)=k6_relat_1(A_96) | ~r1_tarski(A_96, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_369])).
% 8.07/2.71  tff(c_761, plain, (![A_127, C_128, B_129]: (k3_xboole_0(A_127, k10_relat_1(C_128, B_129))=k10_relat_1(k7_relat_1(C_128, A_127), B_129) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.07/2.71  tff(c_777, plain, (![A_45, A_127]: (k10_relat_1(k7_relat_1(k6_relat_1(A_45), A_127), A_45)=k3_xboole_0(A_127, A_45) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_761])).
% 8.07/2.71  tff(c_789, plain, (![A_130, A_131]: (k10_relat_1(k7_relat_1(k6_relat_1(A_130), A_131), A_130)=k3_xboole_0(A_131, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_777])).
% 8.07/2.71  tff(c_801, plain, (![A_97, A_96]: (k3_xboole_0(A_97, A_96)=k10_relat_1(k6_relat_1(A_96), A_96) | ~r1_tarski(A_96, A_97))), inference(superposition, [status(thm), theory('equality')], [c_373, c_789])).
% 8.07/2.71  tff(c_815, plain, (![A_132, A_133]: (k3_xboole_0(A_132, A_133)=A_133 | ~r1_tarski(A_133, A_132))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_801])).
% 8.07/2.71  tff(c_838, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_56, c_815])).
% 8.07/2.71  tff(c_50, plain, (![B_47, A_46]: (r1_tarski(k1_relat_1(k7_relat_1(B_47, A_46)), A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.07/2.71  tff(c_4143, plain, (![A_266, B_267]: (k3_xboole_0(A_266, k1_relat_1(k7_relat_1(B_267, A_266)))=k1_relat_1(k7_relat_1(B_267, A_266)) | ~v1_relat_1(B_267))), inference(resolution, [status(thm)], [c_50, c_815])).
% 8.07/2.71  tff(c_4202, plain, (![A_97, A_96]: (k3_xboole_0(A_97, k1_relat_1(k6_relat_1(A_96)))=k1_relat_1(k7_relat_1(k6_relat_1(A_96), A_97)) | ~v1_relat_1(k6_relat_1(A_96)) | ~r1_tarski(A_96, A_97))), inference(superposition, [status(thm), theory('equality')], [c_373, c_4143])).
% 8.07/2.71  tff(c_4231, plain, (![A_268, A_269]: (k1_relat_1(k7_relat_1(k6_relat_1(A_268), A_269))=k3_xboole_0(A_269, A_268) | ~r1_tarski(A_268, A_269))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46, c_4202])).
% 8.07/2.71  tff(c_282, plain, (![B_87]: (v4_relat_1(B_87, k1_relat_1(B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_8, c_259])).
% 8.07/2.71  tff(c_4314, plain, (![A_268, A_269]: (v4_relat_1(k7_relat_1(k6_relat_1(A_268), A_269), k3_xboole_0(A_269, A_268)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_268), A_269)) | ~r1_tarski(A_268, A_269))), inference(superposition, [status(thm), theory('equality')], [c_4231, c_282])).
% 8.07/2.71  tff(c_7772, plain, (![A_305, A_306]: (v4_relat_1(k7_relat_1(k6_relat_1(A_305), A_306), k3_xboole_0(A_306, A_305)) | ~r1_tarski(A_305, A_306))), inference(demodulation, [status(thm), theory('equality')], [c_3526, c_4314])).
% 8.07/2.71  tff(c_7826, plain, (v4_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')), '#skF_1') | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_838, c_7772])).
% 8.07/2.71  tff(c_7860, plain, (v4_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_7826])).
% 8.07/2.71  tff(c_30, plain, (![B_29, A_28]: (r1_tarski(k1_relat_1(B_29), A_28) | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.07/2.71  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.07/2.71  tff(c_718, plain, (![A_124, A_125]: (r1_tarski(A_124, k1_relat_1('#skF_2')) | ~r1_tarski(A_124, A_125) | ~r1_tarski(A_125, '#skF_1'))), inference(resolution, [status(thm)], [c_347, c_16])).
% 8.07/2.71  tff(c_732, plain, (![B_29, A_28]: (r1_tarski(k1_relat_1(B_29), k1_relat_1('#skF_2')) | ~r1_tarski(A_28, '#skF_1') | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_30, c_718])).
% 8.07/2.71  tff(c_7868, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_7860, c_732])).
% 8.07/2.71  tff(c_7889, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3526, c_8, c_7868])).
% 8.07/2.71  tff(c_7928, plain, (v4_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1('#skF_2')) | ~v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_7889, c_28])).
% 8.07/2.71  tff(c_7975, plain, (v4_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3526, c_7928])).
% 8.07/2.71  tff(c_8097, plain, (v4_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1')) | k4_xboole_0(k1_relat_1(k6_relat_1('#skF_1')), '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1408, c_7975])).
% 8.07/2.71  tff(c_8117, plain, (v4_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_46, c_32, c_8097])).
% 8.07/2.71  tff(c_8144, plain, (k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k6_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_8117, c_44])).
% 8.07/2.71  tff(c_8158, plain, (k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8144])).
% 8.07/2.71  tff(c_1631, plain, (![A_174, B_175]: (r1_tarski(k1_relat_1(k7_relat_1(A_174, k1_relat_1(B_175))), k1_relat_1(k7_relat_1(B_175, k1_relat_1(A_174)))) | ~v1_relat_1(A_174) | ~v1_relat_1(B_175) | ~v1_relat_1(A_174))), inference(superposition, [status(thm), theory('equality')], [c_1598, c_50])).
% 8.07/2.71  tff(c_8565, plain, (r1_tarski(k1_relat_1(k6_relat_1('#skF_1')), k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(k6_relat_1('#skF_1'))))) | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8158, c_1631])).
% 8.07/2.71  tff(c_8679, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_58, c_32, c_46, c_46, c_8565])).
% 8.07/2.71  tff(c_198, plain, (![B_74, A_75]: (r1_tarski(k1_relat_1(k7_relat_1(B_74, A_75)), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.07/2.71  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.07/2.71  tff(c_204, plain, (![B_74, A_75]: (k1_relat_1(k7_relat_1(B_74, A_75))=A_75 | ~r1_tarski(A_75, k1_relat_1(k7_relat_1(B_74, A_75))) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_198, c_4])).
% 8.07/2.71  tff(c_8758, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8679, c_204])).
% 8.07/2.71  tff(c_8793, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8758])).
% 8.07/2.71  tff(c_8944, plain, (v4_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8793, c_282])).
% 8.07/2.71  tff(c_9099, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_8944])).
% 8.07/2.71  tff(c_9102, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_9099])).
% 8.07/2.71  tff(c_9106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_9102])).
% 8.07/2.71  tff(c_9108, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_8944])).
% 8.07/2.71  tff(c_9107, plain, (v4_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_8944])).
% 8.07/2.71  tff(c_9307, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_9107, c_44])).
% 8.07/2.71  tff(c_9313, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9108, c_9307])).
% 8.07/2.71  tff(c_4602, plain, (![A_274, B_275]: (r1_tarski(k1_relat_1(k7_relat_1(A_274, k1_relat_1(B_275))), k1_relat_1(k7_relat_1(B_275, k1_relat_1(A_274)))) | ~v1_relat_1(A_274) | ~v1_relat_1(B_275) | ~v1_relat_1(A_274))), inference(superposition, [status(thm), theory('equality')], [c_1598, c_50])).
% 8.07/2.71  tff(c_324, plain, (![A_91, A_46, B_47]: (r1_tarski(A_91, A_46) | ~r1_tarski(A_91, k1_relat_1(k7_relat_1(B_47, A_46))) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_50, c_312])).
% 8.07/2.71  tff(c_9109, plain, (![A_312, B_313]: (r1_tarski(k1_relat_1(k7_relat_1(A_312, k1_relat_1(B_313))), k1_relat_1(A_312)) | ~v1_relat_1(B_313) | ~v1_relat_1(A_312))), inference(resolution, [status(thm)], [c_4602, c_324])).
% 8.07/2.71  tff(c_9240, plain, (![A_312, A_45]: (r1_tarski(k1_relat_1(k7_relat_1(A_312, A_45)), k1_relat_1(A_312)) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(A_312))), inference(superposition, [status(thm), theory('equality')], [c_46, c_9109])).
% 8.07/2.71  tff(c_9413, plain, (![A_314, A_315]: (r1_tarski(k1_relat_1(k7_relat_1(A_314, A_315)), k1_relat_1(A_314)) | ~v1_relat_1(A_314))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9240])).
% 8.07/2.71  tff(c_9466, plain, (![A_315]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_315)), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8793, c_9413])).
% 8.07/2.71  tff(c_10222, plain, (![A_329]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_329)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9108, c_9466])).
% 8.07/2.71  tff(c_1012, plain, (![A_142, C_143, B_144]: (k9_relat_1(k7_relat_1(A_142, C_143), B_144)=k9_relat_1(A_142, B_144) | ~r1_tarski(B_144, C_143) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.07/2.71  tff(c_36, plain, (![A_33]: (k9_relat_1(A_33, k1_relat_1(A_33))=k2_relat_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.07/2.71  tff(c_1019, plain, (![A_142, C_143]: (k9_relat_1(A_142, k1_relat_1(k7_relat_1(A_142, C_143)))=k2_relat_1(k7_relat_1(A_142, C_143)) | ~v1_relat_1(k7_relat_1(A_142, C_143)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_142, C_143)), C_143) | ~v1_relat_1(A_142))), inference(superposition, [status(thm), theory('equality')], [c_1012, c_36])).
% 8.07/2.71  tff(c_10232, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')))=k2_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_10222, c_1019])).
% 8.07/2.71  tff(c_10298, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9108, c_9108, c_9313, c_9313, c_8793, c_9313, c_10232])).
% 8.07/2.71  tff(c_38, plain, (![A_34, C_38, B_37]: (k9_relat_1(k7_relat_1(A_34, C_38), B_37)=k9_relat_1(A_34, B_37) | ~r1_tarski(B_37, C_38) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.07/2.71  tff(c_10736, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10298, c_38])).
% 8.07/2.71  tff(c_10743, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8, c_10736])).
% 8.07/2.71  tff(c_40, plain, (![A_39]: (k10_relat_1(A_39, k2_relat_1(A_39))=k1_relat_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.07/2.71  tff(c_10808, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10743, c_40])).
% 8.07/2.71  tff(c_10814, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9108, c_8793, c_10808])).
% 8.07/2.71  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.07/2.71  tff(c_767, plain, (![A_127, C_128, B_129]: (k5_xboole_0(A_127, k10_relat_1(k7_relat_1(C_128, A_127), B_129))=k4_xboole_0(A_127, k10_relat_1(C_128, B_129)) | ~v1_relat_1(C_128))), inference(superposition, [status(thm), theory('equality')], [c_761, c_14])).
% 8.07/2.71  tff(c_10996, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10814, c_767])).
% 8.07/2.71  tff(c_11006, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_190, c_10996])).
% 8.07/2.71  tff(c_11008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_11006])).
% 8.07/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/2.71  
% 8.07/2.71  Inference rules
% 8.07/2.71  ----------------------
% 8.07/2.71  #Ref     : 0
% 8.07/2.71  #Sup     : 2410
% 8.07/2.71  #Fact    : 0
% 8.07/2.71  #Define  : 0
% 8.07/2.71  #Split   : 3
% 8.07/2.71  #Chain   : 0
% 8.07/2.71  #Close   : 0
% 8.07/2.71  
% 8.07/2.71  Ordering : KBO
% 8.07/2.71  
% 8.07/2.71  Simplification rules
% 8.07/2.71  ----------------------
% 8.07/2.71  #Subsume      : 620
% 8.07/2.71  #Demod        : 2289
% 8.07/2.71  #Tautology    : 718
% 8.07/2.71  #SimpNegUnit  : 1
% 8.07/2.71  #BackRed      : 8
% 8.07/2.71  
% 8.07/2.71  #Partial instantiations: 0
% 8.07/2.71  #Strategies tried      : 1
% 8.07/2.71  
% 8.07/2.71  Timing (in seconds)
% 8.07/2.72  ----------------------
% 8.07/2.72  Preprocessing        : 0.34
% 8.07/2.72  Parsing              : 0.19
% 8.07/2.72  CNF conversion       : 0.02
% 8.07/2.72  Main loop            : 1.55
% 8.07/2.72  Inferencing          : 0.47
% 8.07/2.72  Reduction            : 0.53
% 8.07/2.72  Demodulation         : 0.39
% 8.07/2.72  BG Simplification    : 0.06
% 8.07/2.72  Subsumption          : 0.39
% 8.07/2.72  Abstraction          : 0.08
% 8.07/2.72  MUC search           : 0.00
% 8.07/2.72  Cooper               : 0.00
% 8.07/2.72  Total                : 1.94
% 8.07/2.72  Index Insertion      : 0.00
% 8.07/2.72  Index Deletion       : 0.00
% 8.07/2.72  Index Matching       : 0.00
% 8.07/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
