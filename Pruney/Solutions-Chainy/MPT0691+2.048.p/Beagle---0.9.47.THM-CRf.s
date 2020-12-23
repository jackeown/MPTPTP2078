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
% DateTime   : Thu Dec  3 10:04:45 EST 2020

% Result     : Theorem 44.89s
% Output     : CNFRefutation 44.89s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 243 expanded)
%              Number of leaves         :   45 ( 103 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 382 expanded)
%              Number of equality atoms :   52 ( 134 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_71,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_109,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_225,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(A_99,B_100)
      | k4_xboole_0(A_99,B_100) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_237,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_66])).

tff(c_70,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(k7_relat_1(A_49,B_50))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60,plain,(
    ! [A_70,B_71] :
      ( k5_relat_1(k6_relat_1(A_70),B_71) = k7_relat_1(B_71,A_70)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1149,plain,(
    ! [A_172,C_173,B_174] :
      ( r1_tarski(k2_xboole_0(A_172,C_173),B_174)
      | ~ r1_tarski(C_173,B_174)
      | ~ r1_tarski(A_172,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_301,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_317,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_301])).

tff(c_1156,plain,(
    ! [B_174,C_173] :
      ( k2_xboole_0(B_174,C_173) = B_174
      | ~ r1_tarski(C_173,B_174)
      | ~ r1_tarski(B_174,B_174) ) ),
    inference(resolution,[status(thm)],[c_1149,c_317])).

tff(c_1194,plain,(
    ! [B_175,C_176] :
      ( k2_xboole_0(B_175,C_176) = B_175
      | ~ r1_tarski(C_176,B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1156])).

tff(c_1249,plain,(
    k2_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1194])).

tff(c_54,plain,(
    ! [A_67] : k1_relat_1(k6_relat_1(A_67)) = A_67 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_386,plain,(
    ! [B_114,A_115] :
      ( r1_tarski(k10_relat_1(B_114,A_115),k1_relat_1(B_114))
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_403,plain,(
    ! [A_67,A_115] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_67),A_115),A_67)
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_386])).

tff(c_432,plain,(
    ! [A_119,A_120] : r1_tarski(k10_relat_1(k6_relat_1(A_119),A_120),A_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_403])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_449,plain,(
    ! [A_119,A_120] : k2_xboole_0(k10_relat_1(k6_relat_1(A_119),A_120),A_119) = A_119 ),
    inference(resolution,[status(thm)],[c_432,c_18])).

tff(c_56,plain,(
    ! [A_67] : k2_relat_1(k6_relat_1(A_67)) = A_67 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_363,plain,(
    ! [A_112] :
      ( k10_relat_1(A_112,k2_relat_1(A_112)) = k1_relat_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_372,plain,(
    ! [A_67] :
      ( k10_relat_1(k6_relat_1(A_67),A_67) = k1_relat_1(k6_relat_1(A_67))
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_363])).

tff(c_376,plain,(
    ! [A_67] : k10_relat_1(k6_relat_1(A_67),A_67) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54,c_372])).

tff(c_3544,plain,(
    ! [C_253,A_254,B_255] :
      ( k2_xboole_0(k10_relat_1(C_253,A_254),k10_relat_1(C_253,B_255)) = k10_relat_1(C_253,k2_xboole_0(A_254,B_255))
      | ~ v1_relat_1(C_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3617,plain,(
    ! [A_67,A_254] :
      ( k2_xboole_0(k10_relat_1(k6_relat_1(A_67),A_254),A_67) = k10_relat_1(k6_relat_1(A_67),k2_xboole_0(A_254,A_67))
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_3544])).

tff(c_3636,plain,(
    ! [A_256,A_257] : k10_relat_1(k6_relat_1(A_256),k2_xboole_0(A_257,A_256)) = A_256 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_449,c_3617])).

tff(c_3748,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_3636])).

tff(c_52,plain,(
    ! [A_64,B_66] :
      ( k10_relat_1(A_64,k1_relat_1(B_66)) = k1_relat_1(k5_relat_1(A_64,B_66))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3821,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3748,c_52])).

tff(c_3879,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_70,c_3821])).

tff(c_3929,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3879])).

tff(c_3936,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3929])).

tff(c_46,plain,(
    ! [B_59,A_58] :
      ( r1_tarski(k10_relat_1(B_59,A_58),k1_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4005,plain,(
    ! [A_58] :
      ( r1_tarski(k10_relat_1(k7_relat_1('#skF_2','#skF_1'),A_58),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3936,c_46])).

tff(c_82848,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4005])).

tff(c_82851,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_82848])).

tff(c_82855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_82851])).

tff(c_82857,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4005])).

tff(c_143,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = k1_xboole_0
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_155,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_412,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_421,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_412])).

tff(c_424,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_421])).

tff(c_640,plain,(
    ! [B_133,A_134] :
      ( k2_relat_1(k7_relat_1(B_133,A_134)) = k9_relat_1(B_133,A_134)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    ! [A_60] :
      ( k10_relat_1(A_60,k2_relat_1(A_60)) = k1_relat_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_19831,plain,(
    ! [B_467,A_468] :
      ( k10_relat_1(k7_relat_1(B_467,A_468),k9_relat_1(B_467,A_468)) = k1_relat_1(k7_relat_1(B_467,A_468))
      | ~ v1_relat_1(k7_relat_1(B_467,A_468))
      | ~ v1_relat_1(B_467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_48])).

tff(c_1665,plain,(
    ! [A_187,C_188,B_189] :
      ( k3_xboole_0(A_187,k10_relat_1(C_188,B_189)) = k10_relat_1(k7_relat_1(C_188,A_187),B_189)
      | ~ v1_relat_1(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1671,plain,(
    ! [A_187,C_188,B_189] :
      ( k5_xboole_0(A_187,k10_relat_1(k7_relat_1(C_188,A_187),B_189)) = k4_xboole_0(A_187,k10_relat_1(C_188,B_189))
      | ~ v1_relat_1(C_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1665,c_14])).

tff(c_202541,plain,(
    ! [A_1488,B_1489] :
      ( k5_xboole_0(A_1488,k1_relat_1(k7_relat_1(B_1489,A_1488))) = k4_xboole_0(A_1488,k10_relat_1(B_1489,k9_relat_1(B_1489,A_1488)))
      | ~ v1_relat_1(B_1489)
      | ~ v1_relat_1(k7_relat_1(B_1489,A_1488))
      | ~ v1_relat_1(B_1489) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19831,c_1671])).

tff(c_202796,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3936,c_202541])).

tff(c_202855,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_82857,c_70,c_424,c_202796])).

tff(c_202857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_202855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 44.89/34.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 44.89/34.90  
% 44.89/34.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 44.89/34.91  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 44.89/34.91  
% 44.89/34.91  %Foreground sorts:
% 44.89/34.91  
% 44.89/34.91  
% 44.89/34.91  %Background operators:
% 44.89/34.91  
% 44.89/34.91  
% 44.89/34.91  %Foreground operators:
% 44.89/34.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 44.89/34.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 44.89/34.91  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 44.89/34.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 44.89/34.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 44.89/34.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 44.89/34.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 44.89/34.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 44.89/34.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 44.89/34.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 44.89/34.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 44.89/34.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 44.89/34.91  tff('#skF_2', type, '#skF_2': $i).
% 44.89/34.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 44.89/34.91  tff('#skF_1', type, '#skF_1': $i).
% 44.89/34.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 44.89/34.91  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 44.89/34.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 44.89/34.91  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 44.89/34.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 44.89/34.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 44.89/34.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 44.89/34.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 44.89/34.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 44.89/34.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 44.89/34.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 44.89/34.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 44.89/34.91  
% 44.89/34.92  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 44.89/34.92  tff(f_132, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 44.89/34.92  tff(f_75, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 44.89/34.92  tff(f_117, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 44.89/34.92  tff(f_71, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 44.89/34.92  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 44.89/34.92  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 44.89/34.92  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 44.89/34.92  tff(f_109, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 44.89/34.92  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 44.89/34.92  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 44.89/34.92  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 44.89/34.92  tff(f_98, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 44.89/34.92  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 44.89/34.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 44.89/34.92  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 44.89/34.92  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 44.89/34.92  tff(f_125, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 44.89/34.92  tff(c_225, plain, (![A_99, B_100]: (r1_tarski(A_99, B_100) | k4_xboole_0(A_99, B_100)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.89/34.92  tff(c_66, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.89/34.92  tff(c_237, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_225, c_66])).
% 44.89/34.92  tff(c_70, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.89/34.92  tff(c_40, plain, (![A_49, B_50]: (v1_relat_1(k7_relat_1(A_49, B_50)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 44.89/34.92  tff(c_60, plain, (![A_70, B_71]: (k5_relat_1(k6_relat_1(A_70), B_71)=k7_relat_1(B_71, A_70) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_117])).
% 44.89/34.92  tff(c_38, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 44.89/34.92  tff(c_68, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.89/34.92  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 44.89/34.92  tff(c_1149, plain, (![A_172, C_173, B_174]: (r1_tarski(k2_xboole_0(A_172, C_173), B_174) | ~r1_tarski(C_173, B_174) | ~r1_tarski(A_172, B_174))), inference(cnfTransformation, [status(thm)], [f_55])).
% 44.89/34.92  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 44.89/34.92  tff(c_301, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_33])).
% 44.89/34.92  tff(c_317, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(k2_xboole_0(A_14, B_15), A_14))), inference(resolution, [status(thm)], [c_20, c_301])).
% 44.89/34.92  tff(c_1156, plain, (![B_174, C_173]: (k2_xboole_0(B_174, C_173)=B_174 | ~r1_tarski(C_173, B_174) | ~r1_tarski(B_174, B_174))), inference(resolution, [status(thm)], [c_1149, c_317])).
% 44.89/34.92  tff(c_1194, plain, (![B_175, C_176]: (k2_xboole_0(B_175, C_176)=B_175 | ~r1_tarski(C_176, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1156])).
% 44.89/34.92  tff(c_1249, plain, (k2_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_1194])).
% 44.89/34.92  tff(c_54, plain, (![A_67]: (k1_relat_1(k6_relat_1(A_67))=A_67)), inference(cnfTransformation, [status(thm)], [f_109])).
% 44.89/34.92  tff(c_386, plain, (![B_114, A_115]: (r1_tarski(k10_relat_1(B_114, A_115), k1_relat_1(B_114)) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_90])).
% 44.89/34.92  tff(c_403, plain, (![A_67, A_115]: (r1_tarski(k10_relat_1(k6_relat_1(A_67), A_115), A_67) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_386])).
% 44.89/34.92  tff(c_432, plain, (![A_119, A_120]: (r1_tarski(k10_relat_1(k6_relat_1(A_119), A_120), A_119))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_403])).
% 44.89/34.92  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 44.89/34.92  tff(c_449, plain, (![A_119, A_120]: (k2_xboole_0(k10_relat_1(k6_relat_1(A_119), A_120), A_119)=A_119)), inference(resolution, [status(thm)], [c_432, c_18])).
% 44.89/34.92  tff(c_56, plain, (![A_67]: (k2_relat_1(k6_relat_1(A_67))=A_67)), inference(cnfTransformation, [status(thm)], [f_109])).
% 44.89/34.92  tff(c_363, plain, (![A_112]: (k10_relat_1(A_112, k2_relat_1(A_112))=k1_relat_1(A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_94])).
% 44.89/34.92  tff(c_372, plain, (![A_67]: (k10_relat_1(k6_relat_1(A_67), A_67)=k1_relat_1(k6_relat_1(A_67)) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_363])).
% 44.89/34.92  tff(c_376, plain, (![A_67]: (k10_relat_1(k6_relat_1(A_67), A_67)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54, c_372])).
% 44.89/34.92  tff(c_3544, plain, (![C_253, A_254, B_255]: (k2_xboole_0(k10_relat_1(C_253, A_254), k10_relat_1(C_253, B_255))=k10_relat_1(C_253, k2_xboole_0(A_254, B_255)) | ~v1_relat_1(C_253))), inference(cnfTransformation, [status(thm)], [f_98])).
% 44.89/34.92  tff(c_3617, plain, (![A_67, A_254]: (k2_xboole_0(k10_relat_1(k6_relat_1(A_67), A_254), A_67)=k10_relat_1(k6_relat_1(A_67), k2_xboole_0(A_254, A_67)) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_376, c_3544])).
% 44.89/34.92  tff(c_3636, plain, (![A_256, A_257]: (k10_relat_1(k6_relat_1(A_256), k2_xboole_0(A_257, A_256))=A_256)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_449, c_3617])).
% 44.89/34.92  tff(c_3748, plain, (k10_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1249, c_3636])).
% 44.89/34.92  tff(c_52, plain, (![A_64, B_66]: (k10_relat_1(A_64, k1_relat_1(B_66))=k1_relat_1(k5_relat_1(A_64, B_66)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_105])).
% 44.89/34.92  tff(c_3821, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3748, c_52])).
% 44.89/34.92  tff(c_3879, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_70, c_3821])).
% 44.89/34.92  tff(c_3929, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_60, c_3879])).
% 44.89/34.92  tff(c_3936, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3929])).
% 44.89/34.92  tff(c_46, plain, (![B_59, A_58]: (r1_tarski(k10_relat_1(B_59, A_58), k1_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_90])).
% 44.89/34.92  tff(c_4005, plain, (![A_58]: (r1_tarski(k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_58), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3936, c_46])).
% 44.89/34.92  tff(c_82848, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4005])).
% 44.89/34.92  tff(c_82851, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_82848])).
% 44.89/34.92  tff(c_82855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_82851])).
% 44.89/34.92  tff(c_82857, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_4005])).
% 44.89/34.92  tff(c_143, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=k1_xboole_0 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.89/34.92  tff(c_155, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_143])).
% 44.89/34.92  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 44.89/34.92  tff(c_412, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k4_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_39])).
% 44.89/34.92  tff(c_421, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_412])).
% 44.89/34.92  tff(c_424, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_421])).
% 44.89/34.92  tff(c_640, plain, (![B_133, A_134]: (k2_relat_1(k7_relat_1(B_133, A_134))=k9_relat_1(B_133, A_134) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_79])).
% 44.89/34.92  tff(c_48, plain, (![A_60]: (k10_relat_1(A_60, k2_relat_1(A_60))=k1_relat_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_94])).
% 44.89/34.92  tff(c_19831, plain, (![B_467, A_468]: (k10_relat_1(k7_relat_1(B_467, A_468), k9_relat_1(B_467, A_468))=k1_relat_1(k7_relat_1(B_467, A_468)) | ~v1_relat_1(k7_relat_1(B_467, A_468)) | ~v1_relat_1(B_467))), inference(superposition, [status(thm), theory('equality')], [c_640, c_48])).
% 44.89/34.92  tff(c_1665, plain, (![A_187, C_188, B_189]: (k3_xboole_0(A_187, k10_relat_1(C_188, B_189))=k10_relat_1(k7_relat_1(C_188, A_187), B_189) | ~v1_relat_1(C_188))), inference(cnfTransformation, [status(thm)], [f_125])).
% 44.89/34.92  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 44.89/34.92  tff(c_1671, plain, (![A_187, C_188, B_189]: (k5_xboole_0(A_187, k10_relat_1(k7_relat_1(C_188, A_187), B_189))=k4_xboole_0(A_187, k10_relat_1(C_188, B_189)) | ~v1_relat_1(C_188))), inference(superposition, [status(thm), theory('equality')], [c_1665, c_14])).
% 44.89/34.92  tff(c_202541, plain, (![A_1488, B_1489]: (k5_xboole_0(A_1488, k1_relat_1(k7_relat_1(B_1489, A_1488)))=k4_xboole_0(A_1488, k10_relat_1(B_1489, k9_relat_1(B_1489, A_1488))) | ~v1_relat_1(B_1489) | ~v1_relat_1(k7_relat_1(B_1489, A_1488)) | ~v1_relat_1(B_1489))), inference(superposition, [status(thm), theory('equality')], [c_19831, c_1671])).
% 44.89/34.92  tff(c_202796, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3936, c_202541])).
% 44.89/34.92  tff(c_202855, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_82857, c_70, c_424, c_202796])).
% 44.89/34.92  tff(c_202857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_202855])).
% 44.89/34.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 44.89/34.92  
% 44.89/34.92  Inference rules
% 44.89/34.92  ----------------------
% 44.89/34.92  #Ref     : 0
% 44.89/34.92  #Sup     : 48799
% 44.89/34.92  #Fact    : 0
% 44.89/34.92  #Define  : 0
% 44.89/34.92  #Split   : 4
% 44.89/34.92  #Chain   : 0
% 44.89/34.92  #Close   : 0
% 44.89/34.92  
% 44.89/34.92  Ordering : KBO
% 44.89/34.92  
% 44.89/34.92  Simplification rules
% 44.89/34.92  ----------------------
% 44.89/34.92  #Subsume      : 10922
% 44.89/34.92  #Demod        : 37376
% 44.89/34.92  #Tautology    : 18831
% 44.89/34.92  #SimpNegUnit  : 1
% 44.89/34.92  #BackRed      : 1
% 44.89/34.92  
% 44.89/34.92  #Partial instantiations: 0
% 44.89/34.92  #Strategies tried      : 1
% 44.89/34.92  
% 44.89/34.92  Timing (in seconds)
% 44.89/34.92  ----------------------
% 44.89/34.93  Preprocessing        : 0.35
% 44.89/34.93  Parsing              : 0.19
% 44.89/34.93  CNF conversion       : 0.02
% 44.89/34.93  Main loop            : 33.79
% 44.89/34.93  Inferencing          : 3.61
% 44.89/34.93  Reduction            : 17.56
% 44.89/34.93  Demodulation         : 15.60
% 44.89/34.93  BG Simplification    : 0.42
% 44.89/34.93  Subsumption          : 10.85
% 44.89/34.93  Abstraction          : 0.69
% 44.89/34.93  MUC search           : 0.00
% 44.89/34.93  Cooper               : 0.00
% 44.89/34.93  Total                : 34.18
% 44.89/34.93  Index Insertion      : 0.00
% 44.89/34.93  Index Deletion       : 0.00
% 44.89/34.93  Index Matching       : 0.00
% 44.89/34.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
