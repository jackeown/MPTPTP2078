%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:45 EST 2020

% Result     : Theorem 34.32s
% Output     : CNFRefutation 34.52s
% Verified   : 
% Statistics : Number of formulae       :  181 (43781 expanded)
%              Number of leaves         :   38 (15578 expanded)
%              Depth                    :   37
%              Number of atoms          :  310 (72392 expanded)
%              Number of equality atoms :  110 (35278 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_50,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    ! [A_45,B_46] :
      ( k5_relat_1(k6_relat_1(A_45),B_46) = k7_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_193,plain,(
    ! [A_73,B_74] :
      ( k5_relat_1(k6_relat_1(A_73),B_74) = k7_relat_1(B_74,A_73)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k5_relat_1(A_24,B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_199,plain,(
    ! [B_74,A_73] :
      ( v1_relat_1(k7_relat_1(B_74,A_73))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(k6_relat_1(A_73))
      | ~ v1_relat_1(B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_22])).

tff(c_205,plain,(
    ! [B_74,A_73] :
      ( v1_relat_1(k7_relat_1(B_74,A_73))
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_199])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_230,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(A_84,C_85)
      | ~ r1_tarski(B_86,C_85)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_84,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_230])).

tff(c_38,plain,(
    ! [A_42] : k1_relat_1(k6_relat_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    ! [A_42] : k2_relat_1(k6_relat_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_103,plain,(
    ! [A_61] :
      ( k10_relat_1(A_61,k2_relat_1(A_61)) = k1_relat_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_112,plain,(
    ! [A_42] :
      ( k10_relat_1(k6_relat_1(A_42),A_42) = k1_relat_1(k6_relat_1(A_42))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_103])).

tff(c_116,plain,(
    ! [A_42] : k10_relat_1(k6_relat_1(A_42),A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38,c_112])).

tff(c_341,plain,(
    ! [B_96,A_97] :
      ( k7_relat_1(B_96,A_97) = B_96
      | ~ r1_tarski(k1_relat_1(B_96),A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_354,plain,(
    ! [A_42,A_97] :
      ( k7_relat_1(k6_relat_1(A_42),A_97) = k6_relat_1(A_42)
      | ~ r1_tarski(A_42,A_97)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_341])).

tff(c_363,plain,(
    ! [A_42,A_97] :
      ( k7_relat_1(k6_relat_1(A_42),A_97) = k6_relat_1(A_42)
      | ~ r1_tarski(A_42,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_354])).

tff(c_804,plain,(
    ! [A_128,C_129,B_130] :
      ( k3_xboole_0(A_128,k10_relat_1(C_129,B_130)) = k10_relat_1(k7_relat_1(C_129,A_128),B_130)
      | ~ v1_relat_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_817,plain,(
    ! [A_42,A_128] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_42),A_128),A_42) = k3_xboole_0(A_128,A_42)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_804])).

tff(c_829,plain,(
    ! [A_131,A_132] : k10_relat_1(k7_relat_1(k6_relat_1(A_131),A_132),A_131) = k3_xboole_0(A_132,A_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_817])).

tff(c_853,plain,(
    ! [A_97,A_42] :
      ( k3_xboole_0(A_97,A_42) = k10_relat_1(k6_relat_1(A_42),A_42)
      | ~ r1_tarski(A_42,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_829])).

tff(c_868,plain,(
    ! [A_133,A_134] :
      ( k3_xboole_0(A_133,A_134) = A_134
      | ~ r1_tarski(A_134,A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_853])).

tff(c_910,plain,(
    ! [A_84] :
      ( k3_xboole_0(k1_relat_1('#skF_2'),A_84) = A_84
      | ~ r1_tarski(A_84,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_247,c_868])).

tff(c_828,plain,(
    ! [A_42,A_128] : k10_relat_1(k7_relat_1(k6_relat_1(A_42),A_128),A_42) = k3_xboole_0(A_128,A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_817])).

tff(c_2059,plain,(
    ! [B_182,C_183,A_184] :
      ( k10_relat_1(k5_relat_1(B_182,C_183),A_184) = k10_relat_1(B_182,k10_relat_1(C_183,A_184))
      | ~ v1_relat_1(C_183)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2098,plain,(
    ! [A_45,B_46,A_184] :
      ( k10_relat_1(k6_relat_1(A_45),k10_relat_1(B_46,A_184)) = k10_relat_1(k7_relat_1(B_46,A_45),A_184)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2059])).

tff(c_6619,plain,(
    ! [A_311,B_312,A_313] :
      ( k10_relat_1(k6_relat_1(A_311),k10_relat_1(B_312,A_313)) = k10_relat_1(k7_relat_1(B_312,A_311),A_313)
      | ~ v1_relat_1(B_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2098])).

tff(c_6848,plain,(
    ! [A_42,A_311] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_42),A_311),A_42) = k10_relat_1(k6_relat_1(A_311),A_42)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6619])).

tff(c_6897,plain,(
    ! [A_311,A_42] : k10_relat_1(k6_relat_1(A_311),A_42) = k3_xboole_0(A_311,A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_828,c_6848])).

tff(c_150,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k10_relat_1(B_67,A_68),k1_relat_1(B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_159,plain,(
    ! [A_42,A_68] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_42),A_68),A_42)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_150])).

tff(c_164,plain,(
    ! [A_42,A_68] : r1_tarski(k10_relat_1(k6_relat_1(A_42),A_68),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_159])).

tff(c_6939,plain,(
    ! [A_42,A_68] : r1_tarski(k3_xboole_0(A_42,A_68),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6897,c_164])).

tff(c_1160,plain,(
    ! [A_145,B_146] :
      ( k10_relat_1(A_145,k1_relat_1(B_146)) = k1_relat_1(k5_relat_1(A_145,B_146))
      | ~ v1_relat_1(B_146)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1240,plain,(
    ! [A_145,A_42] :
      ( k1_relat_1(k5_relat_1(A_145,k6_relat_1(A_42))) = k10_relat_1(A_145,A_42)
      | ~ v1_relat_1(k6_relat_1(A_42))
      | ~ v1_relat_1(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1160])).

tff(c_1310,plain,(
    ! [A_149,A_150] :
      ( k1_relat_1(k5_relat_1(A_149,k6_relat_1(A_150))) = k10_relat_1(A_149,A_150)
      | ~ v1_relat_1(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1240])).

tff(c_1351,plain,(
    ! [A_150,A_45] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_150),A_45)) = k10_relat_1(k6_relat_1(A_45),A_150)
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(k6_relat_1(A_150)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1310])).

tff(c_1357,plain,(
    ! [A_150,A_45] : k1_relat_1(k7_relat_1(k6_relat_1(A_150),A_45)) = k10_relat_1(k6_relat_1(A_45),A_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_1351])).

tff(c_6932,plain,(
    ! [A_150,A_45] : k1_relat_1(k7_relat_1(k6_relat_1(A_150),A_45)) = k3_xboole_0(A_45,A_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6897,c_1357])).

tff(c_915,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_868])).

tff(c_48,plain,(
    ! [A_49,C_51,B_50] :
      ( k3_xboole_0(A_49,k10_relat_1(C_51,B_50)) = k10_relat_1(k7_relat_1(C_51,A_49),B_50)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_208,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_77,A_78)),k1_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_213,plain,(
    ! [A_42,A_78] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_42),A_78)),A_42)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_208])).

tff(c_216,plain,(
    ! [A_42,A_78] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_42),A_78)),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_213])).

tff(c_1452,plain,(
    ! [A_155,A_156] : r1_tarski(k10_relat_1(k6_relat_1(A_155),A_156),A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_216])).

tff(c_864,plain,(
    ! [A_97,A_42] :
      ( k3_xboole_0(A_97,A_42) = A_42
      | ~ r1_tarski(A_42,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_853])).

tff(c_2536,plain,(
    ! [A_201,A_202] : k3_xboole_0(A_201,k10_relat_1(k6_relat_1(A_202),A_201)) = k10_relat_1(k6_relat_1(A_202),A_201) ),
    inference(resolution,[status(thm)],[c_1452,c_864])).

tff(c_2583,plain,(
    ! [A_202,B_50] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_202),B_50),B_50) = k10_relat_1(k6_relat_1(A_202),B_50)
      | ~ v1_relat_1(k6_relat_1(A_202)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2536])).

tff(c_2608,plain,(
    ! [A_202,B_50] : k10_relat_1(k7_relat_1(k6_relat_1(A_202),B_50),B_50) = k10_relat_1(k6_relat_1(A_202),B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2583])).

tff(c_6919,plain,(
    ! [A_202,B_50] : k10_relat_1(k7_relat_1(k6_relat_1(A_202),B_50),B_50) = k3_xboole_0(A_202,B_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6897,c_2608])).

tff(c_6940,plain,(
    ! [A_314,A_315] : k10_relat_1(k6_relat_1(A_314),A_315) = k3_xboole_0(A_314,A_315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_828,c_6848])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_811,plain,(
    ! [C_129,B_130] :
      ( k10_relat_1(k7_relat_1(C_129,k10_relat_1(C_129,B_130)),B_130) = k10_relat_1(C_129,B_130)
      | ~ v1_relat_1(C_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_2])).

tff(c_6949,plain,(
    ! [A_314,A_315] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_314),k3_xboole_0(A_314,A_315)),A_315) = k10_relat_1(k6_relat_1(A_314),A_315)
      | ~ v1_relat_1(k6_relat_1(A_314)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6940,c_811])).

tff(c_22601,plain,(
    ! [A_682,A_683] : k10_relat_1(k7_relat_1(k6_relat_1(A_682),k3_xboole_0(A_682,A_683)),A_683) = k3_xboole_0(A_682,A_683) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6897,c_6949])).

tff(c_22744,plain,(
    k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_1'),'#skF_1') = k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_22601])).

tff(c_22803,plain,(
    k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_1'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_22744])).

tff(c_30,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k10_relat_1(B_33,A_32),k1_relat_1(B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_176,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_186,plain,(
    ! [B_33,A_32] :
      ( k10_relat_1(B_33,A_32) = k1_relat_1(B_33)
      | ~ r1_tarski(k1_relat_1(B_33),k10_relat_1(B_33,A_32))
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_30,c_176])).

tff(c_22856,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_1'),'#skF_1') = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_1'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_1')),'#skF_1')
    | ~ v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22803,c_186])).

tff(c_22907,plain,
    ( k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6939,c_6932,c_915,c_6919,c_6932,c_22856])).

tff(c_33309,plain,(
    ~ v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_22907])).

tff(c_33315,plain,(
    ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_205,c_33309])).

tff(c_33321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_33315])).

tff(c_33322,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22907])).

tff(c_6962,plain,(
    ! [A_314,A_49,A_315] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_314),A_49),A_315) = k3_xboole_0(A_49,k3_xboole_0(A_314,A_315))
      | ~ v1_relat_1(k6_relat_1(A_314)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6940,c_48])).

tff(c_7003,plain,(
    ! [A_314,A_49,A_315] : k10_relat_1(k7_relat_1(k6_relat_1(A_314),A_49),A_315) = k3_xboole_0(A_49,k3_xboole_0(A_314,A_315)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6962])).

tff(c_9257,plain,(
    ! [A_393,A_394,B_395] :
      ( k3_xboole_0(A_393,k1_relat_1(k5_relat_1(A_394,B_395))) = k10_relat_1(k7_relat_1(A_394,A_393),k1_relat_1(B_395))
      | ~ v1_relat_1(A_394)
      | ~ v1_relat_1(B_395)
      | ~ v1_relat_1(A_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1160,c_48])).

tff(c_9377,plain,(
    ! [A_45,A_393,B_46] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_45),A_393),k1_relat_1(B_46)) = k3_xboole_0(A_393,k1_relat_1(k7_relat_1(B_46,A_45)))
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_9257])).

tff(c_9391,plain,(
    ! [A_45,A_393,B_46] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_45),A_393),k1_relat_1(B_46)) = k3_xboole_0(A_393,k1_relat_1(k7_relat_1(B_46,A_45)))
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_9377])).

tff(c_26905,plain,(
    ! [A_393,A_45,B_46] :
      ( k3_xboole_0(A_393,k3_xboole_0(A_45,k1_relat_1(B_46))) = k3_xboole_0(A_393,k1_relat_1(k7_relat_1(B_46,A_45)))
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7003,c_9391])).

tff(c_33377,plain,(
    ! [A_393] :
      ( k3_xboole_0(A_393,k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0(A_393,'#skF_1')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33322,c_26905])).

tff(c_33784,plain,(
    ! [A_841] : k3_xboole_0(A_841,k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0(A_841,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_33377])).

tff(c_1363,plain,(
    ! [A_78,A_42] : r1_tarski(k10_relat_1(k6_relat_1(A_78),A_42),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_216])).

tff(c_6931,plain,(
    ! [A_78,A_42] : r1_tarski(k3_xboole_0(A_78,A_42),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6897,c_1363])).

tff(c_34443,plain,(
    ! [A_842] : r1_tarski(k3_xboole_0(A_842,'#skF_1'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33784,c_6931])).

tff(c_34471,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_34443])).

tff(c_34497,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34471])).

tff(c_34535,plain,(
    k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34497,c_864])).

tff(c_34335,plain,(
    k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1') = k1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_33784])).

tff(c_35165,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34535,c_34335])).

tff(c_35294,plain,(
    ! [A_32] :
      ( r1_tarski(k10_relat_1(k7_relat_1('#skF_2','#skF_1'),A_32),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35165,c_30])).

tff(c_43601,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_35294])).

tff(c_43604,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_205,c_43601])).

tff(c_43608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_43604])).

tff(c_43610,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_35294])).

tff(c_364,plain,(
    ! [B_96] :
      ( k7_relat_1(B_96,k1_relat_1(B_96)) = B_96
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_8,c_341])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8481,plain,(
    ! [B_367,A_368] :
      ( k1_relat_1(k7_relat_1(B_367,A_368)) = k1_relat_1(B_367)
      | ~ r1_tarski(k1_relat_1(B_367),k1_relat_1(k7_relat_1(B_367,A_368)))
      | ~ v1_relat_1(B_367) ) ),
    inference(resolution,[status(thm)],[c_208,c_4])).

tff(c_8522,plain,(
    ! [B_96] :
      ( k1_relat_1(k7_relat_1(B_96,k1_relat_1(B_96))) = k1_relat_1(B_96)
      | ~ r1_tarski(k1_relat_1(B_96),k1_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_8481])).

tff(c_8541,plain,(
    ! [B_96] :
      ( k1_relat_1(k7_relat_1(B_96,k1_relat_1(B_96))) = k1_relat_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8522])).

tff(c_35234,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35165,c_8541])).

tff(c_35313,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35165,c_35234])).

tff(c_45472,plain,(
    k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43610,c_35313])).

tff(c_26906,plain,(
    ! [A_739,A_740,B_741] :
      ( k3_xboole_0(A_739,k3_xboole_0(A_740,k1_relat_1(B_741))) = k3_xboole_0(A_739,k1_relat_1(k7_relat_1(B_741,A_740)))
      | ~ v1_relat_1(B_741) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7003,c_9391])).

tff(c_7082,plain,(
    ! [A_318,A_319] : r1_tarski(k3_xboole_0(A_318,A_319),A_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6897,c_164])).

tff(c_7136,plain,(
    ! [A_318,A_319] : k3_xboole_0(A_318,k3_xboole_0(A_318,A_319)) = k3_xboole_0(A_318,A_319) ),
    inference(resolution,[status(thm)],[c_7082,c_864])).

tff(c_106584,plain,(
    ! [A_1402,B_1403] :
      ( k3_xboole_0(A_1402,k1_relat_1(k7_relat_1(B_1403,A_1402))) = k3_xboole_0(A_1402,k1_relat_1(B_1403))
      | ~ v1_relat_1(B_1403) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26906,c_7136])).

tff(c_107796,plain,(
    ! [A_1404,B_1405] :
      ( r1_tarski(k3_xboole_0(A_1404,k1_relat_1(B_1405)),k1_relat_1(k7_relat_1(B_1405,A_1404)))
      | ~ v1_relat_1(B_1405) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106584,c_6931])).

tff(c_108015,plain,(
    ! [B_1406] :
      ( r1_tarski(k1_relat_1(B_1406),k1_relat_1(k7_relat_1(B_1406,k1_relat_1(B_1406))))
      | ~ v1_relat_1(B_1406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107796])).

tff(c_46,plain,(
    ! [B_48,A_47] :
      ( k7_relat_1(B_48,A_47) = B_48
      | ~ r1_tarski(k1_relat_1(B_48),A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_109922,plain,(
    ! [B_1417] :
      ( k7_relat_1(B_1417,k1_relat_1(k7_relat_1(B_1417,k1_relat_1(B_1417)))) = B_1417
      | ~ v1_relat_1(B_1417) ) ),
    inference(resolution,[status(thm)],[c_108015,c_46])).

tff(c_110148,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))) = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35165,c_109922])).

tff(c_110230,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43610,c_45472,c_110148])).

tff(c_32,plain,(
    ! [A_34] :
      ( k10_relat_1(A_34,k2_relat_1(A_34)) = k1_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_820,plain,(
    ! [A_34,A_128] :
      ( k10_relat_1(k7_relat_1(A_34,A_128),k2_relat_1(A_34)) = k3_xboole_0(A_128,k1_relat_1(A_34))
      | ~ v1_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_804])).

tff(c_110376,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110230,c_820])).

tff(c_110490,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43610,c_43610,c_2,c_35165,c_110376])).

tff(c_6660,plain,(
    ! [A_311,B_312,A_313] :
      ( k10_relat_1(k6_relat_1(A_311),k10_relat_1(B_312,A_313)) = k1_relat_1(k6_relat_1(A_311))
      | ~ r1_tarski(k1_relat_1(k6_relat_1(A_311)),k10_relat_1(k7_relat_1(B_312,A_311),A_313))
      | ~ v1_relat_1(k6_relat_1(A_311))
      | ~ v1_relat_1(B_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6619,c_186])).

tff(c_6864,plain,(
    ! [A_311,B_312,A_313] :
      ( k10_relat_1(k6_relat_1(A_311),k10_relat_1(B_312,A_313)) = A_311
      | ~ r1_tarski(A_311,k10_relat_1(k7_relat_1(B_312,A_311),A_313))
      | ~ v1_relat_1(B_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38,c_38,c_6660])).

tff(c_32767,plain,(
    ! [A_311,B_312,A_313] :
      ( k3_xboole_0(A_311,k10_relat_1(B_312,A_313)) = A_311
      | ~ r1_tarski(A_311,k10_relat_1(k7_relat_1(B_312,A_311),A_313))
      | ~ v1_relat_1(B_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6897,c_6864])).

tff(c_113230,plain,
    ( k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_110490,c_32767])).

tff(c_113369,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8,c_113230])).

tff(c_10272,plain,(
    ! [B_429,C_430] :
      ( k10_relat_1(B_429,k10_relat_1(C_430,k2_relat_1(k5_relat_1(B_429,C_430)))) = k1_relat_1(k5_relat_1(B_429,C_430))
      | ~ v1_relat_1(k5_relat_1(B_429,C_430))
      | ~ v1_relat_1(C_430)
      | ~ v1_relat_1(B_429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2059,c_32])).

tff(c_10344,plain,(
    ! [A_45,B_46] :
      ( k10_relat_1(k6_relat_1(A_45),k10_relat_1(B_46,k2_relat_1(k7_relat_1(B_46,A_45)))) = k1_relat_1(k5_relat_1(k6_relat_1(A_45),B_46))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_45),B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10272])).

tff(c_10355,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,k10_relat_1(B_46,k2_relat_1(k7_relat_1(B_46,A_45)))) = k1_relat_1(k5_relat_1(k6_relat_1(A_45),B_46))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_45),B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6897,c_10344])).

tff(c_113865,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1'
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_113369,c_10355])).

tff(c_114230,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1'
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_113865])).

tff(c_129789,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_114230])).

tff(c_129792,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_129789])).

tff(c_129798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_43610,c_129792])).

tff(c_129800,plain,(
    v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_114230])).

tff(c_126,plain,(
    ! [A_63] :
      ( k9_relat_1(A_63,k1_relat_1(A_63)) = k2_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_135,plain,(
    ! [A_42] :
      ( k9_relat_1(k6_relat_1(A_42),A_42) = k2_relat_1(k6_relat_1(A_42))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_126])).

tff(c_139,plain,(
    ! [A_42] : k9_relat_1(k6_relat_1(A_42),A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_40,c_135])).

tff(c_129799,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_114230])).

tff(c_2454,plain,(
    ! [B_196,C_197,A_198] :
      ( k9_relat_1(k5_relat_1(B_196,C_197),A_198) = k9_relat_1(C_197,k9_relat_1(B_196,A_198))
      | ~ v1_relat_1(C_197)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_27] :
      ( k9_relat_1(A_27,k1_relat_1(A_27)) = k2_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2461,plain,(
    ! [C_197,B_196] :
      ( k9_relat_1(C_197,k9_relat_1(B_196,k1_relat_1(k5_relat_1(B_196,C_197)))) = k2_relat_1(k5_relat_1(B_196,C_197))
      | ~ v1_relat_1(k5_relat_1(B_196,C_197))
      | ~ v1_relat_1(C_197)
      | ~ v1_relat_1(B_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2454,c_26])).

tff(c_130184,plain,
    ( k9_relat_1('#skF_2',k9_relat_1(k6_relat_1('#skF_1'),'#skF_1')) = k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_129799,c_2461])).

tff(c_130350,plain,(
    k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_54,c_129800,c_139,c_130184])).

tff(c_130421,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_130350])).

tff(c_130439,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_130421])).

tff(c_7018,plain,(
    ! [A_316,A_317] : r1_tarski(k3_xboole_0(A_316,A_317),A_317) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6897,c_1363])).

tff(c_7063,plain,(
    ! [C_51,A_49,B_50] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_51,A_49),B_50),k10_relat_1(C_51,B_50))
      | ~ v1_relat_1(C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_7018])).

tff(c_113251,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_110490,c_7063])).

tff(c_113383,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_113251])).

tff(c_130446,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130439,c_113383])).

tff(c_130449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_130446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.32/23.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.32/24.01  
% 34.32/24.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.32/24.02  %$ r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 34.32/24.02  
% 34.32/24.02  %Foreground sorts:
% 34.32/24.02  
% 34.32/24.02  
% 34.32/24.02  %Background operators:
% 34.32/24.02  
% 34.32/24.02  
% 34.32/24.02  %Foreground operators:
% 34.32/24.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.32/24.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 34.32/24.02  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 34.32/24.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 34.32/24.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.32/24.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 34.32/24.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 34.32/24.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 34.32/24.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 34.32/24.02  tff('#skF_2', type, '#skF_2': $i).
% 34.32/24.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 34.32/24.02  tff('#skF_1', type, '#skF_1': $i).
% 34.32/24.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 34.32/24.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.32/24.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 34.32/24.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.32/24.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 34.32/24.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.32/24.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 34.32/24.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 34.32/24.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 34.32/24.02  
% 34.52/24.04  tff(f_119, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 34.52/24.04  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 34.52/24.04  tff(f_57, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 34.52/24.04  tff(f_55, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 34.52/24.04  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 34.52/24.04  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 34.52/24.04  tff(f_94, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 34.52/24.04  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 34.52/24.04  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 34.52/24.04  tff(f_112, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 34.52/24.04  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 34.52/24.04  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 34.52/24.04  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 34.52/24.04  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 34.52/24.04  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 34.52/24.04  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 34.52/24.04  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 34.52/24.04  tff(c_50, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 34.52/24.04  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 34.52/24.04  tff(c_44, plain, (![A_45, B_46]: (k5_relat_1(k6_relat_1(A_45), B_46)=k7_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_102])).
% 34.52/24.04  tff(c_24, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 34.52/24.04  tff(c_193, plain, (![A_73, B_74]: (k5_relat_1(k6_relat_1(A_73), B_74)=k7_relat_1(B_74, A_73) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_102])).
% 34.52/24.04  tff(c_22, plain, (![A_24, B_25]: (v1_relat_1(k5_relat_1(A_24, B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 34.52/24.04  tff(c_199, plain, (![B_74, A_73]: (v1_relat_1(k7_relat_1(B_74, A_73)) | ~v1_relat_1(B_74) | ~v1_relat_1(k6_relat_1(A_73)) | ~v1_relat_1(B_74))), inference(superposition, [status(thm), theory('equality')], [c_193, c_22])).
% 34.52/24.04  tff(c_205, plain, (![B_74, A_73]: (v1_relat_1(k7_relat_1(B_74, A_73)) | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_199])).
% 34.52/24.04  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.52/24.04  tff(c_52, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 34.52/24.04  tff(c_230, plain, (![A_84, C_85, B_86]: (r1_tarski(A_84, C_85) | ~r1_tarski(B_86, C_85) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_39])).
% 34.52/24.04  tff(c_247, plain, (![A_84]: (r1_tarski(A_84, k1_relat_1('#skF_2')) | ~r1_tarski(A_84, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_230])).
% 34.52/24.04  tff(c_38, plain, (![A_42]: (k1_relat_1(k6_relat_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_94])).
% 34.52/24.04  tff(c_40, plain, (![A_42]: (k2_relat_1(k6_relat_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_94])).
% 34.52/24.04  tff(c_103, plain, (![A_61]: (k10_relat_1(A_61, k2_relat_1(A_61))=k1_relat_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 34.52/24.04  tff(c_112, plain, (![A_42]: (k10_relat_1(k6_relat_1(A_42), A_42)=k1_relat_1(k6_relat_1(A_42)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_103])).
% 34.52/24.04  tff(c_116, plain, (![A_42]: (k10_relat_1(k6_relat_1(A_42), A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38, c_112])).
% 34.52/24.04  tff(c_341, plain, (![B_96, A_97]: (k7_relat_1(B_96, A_97)=B_96 | ~r1_tarski(k1_relat_1(B_96), A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_108])).
% 34.52/24.04  tff(c_354, plain, (![A_42, A_97]: (k7_relat_1(k6_relat_1(A_42), A_97)=k6_relat_1(A_42) | ~r1_tarski(A_42, A_97) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_341])).
% 34.52/24.04  tff(c_363, plain, (![A_42, A_97]: (k7_relat_1(k6_relat_1(A_42), A_97)=k6_relat_1(A_42) | ~r1_tarski(A_42, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_354])).
% 34.52/24.04  tff(c_804, plain, (![A_128, C_129, B_130]: (k3_xboole_0(A_128, k10_relat_1(C_129, B_130))=k10_relat_1(k7_relat_1(C_129, A_128), B_130) | ~v1_relat_1(C_129))), inference(cnfTransformation, [status(thm)], [f_112])).
% 34.52/24.04  tff(c_817, plain, (![A_42, A_128]: (k10_relat_1(k7_relat_1(k6_relat_1(A_42), A_128), A_42)=k3_xboole_0(A_128, A_42) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_804])).
% 34.52/24.04  tff(c_829, plain, (![A_131, A_132]: (k10_relat_1(k7_relat_1(k6_relat_1(A_131), A_132), A_131)=k3_xboole_0(A_132, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_817])).
% 34.52/24.04  tff(c_853, plain, (![A_97, A_42]: (k3_xboole_0(A_97, A_42)=k10_relat_1(k6_relat_1(A_42), A_42) | ~r1_tarski(A_42, A_97))), inference(superposition, [status(thm), theory('equality')], [c_363, c_829])).
% 34.52/24.04  tff(c_868, plain, (![A_133, A_134]: (k3_xboole_0(A_133, A_134)=A_134 | ~r1_tarski(A_134, A_133))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_853])).
% 34.52/24.04  tff(c_910, plain, (![A_84]: (k3_xboole_0(k1_relat_1('#skF_2'), A_84)=A_84 | ~r1_tarski(A_84, '#skF_1'))), inference(resolution, [status(thm)], [c_247, c_868])).
% 34.52/24.04  tff(c_828, plain, (![A_42, A_128]: (k10_relat_1(k7_relat_1(k6_relat_1(A_42), A_128), A_42)=k3_xboole_0(A_128, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_817])).
% 34.52/24.04  tff(c_2059, plain, (![B_182, C_183, A_184]: (k10_relat_1(k5_relat_1(B_182, C_183), A_184)=k10_relat_1(B_182, k10_relat_1(C_183, A_184)) | ~v1_relat_1(C_183) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_83])).
% 34.52/24.04  tff(c_2098, plain, (![A_45, B_46, A_184]: (k10_relat_1(k6_relat_1(A_45), k10_relat_1(B_46, A_184))=k10_relat_1(k7_relat_1(B_46, A_45), A_184) | ~v1_relat_1(B_46) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2059])).
% 34.52/24.04  tff(c_6619, plain, (![A_311, B_312, A_313]: (k10_relat_1(k6_relat_1(A_311), k10_relat_1(B_312, A_313))=k10_relat_1(k7_relat_1(B_312, A_311), A_313) | ~v1_relat_1(B_312))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2098])).
% 34.52/24.04  tff(c_6848, plain, (![A_42, A_311]: (k10_relat_1(k7_relat_1(k6_relat_1(A_42), A_311), A_42)=k10_relat_1(k6_relat_1(A_311), A_42) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_6619])).
% 34.52/24.04  tff(c_6897, plain, (![A_311, A_42]: (k10_relat_1(k6_relat_1(A_311), A_42)=k3_xboole_0(A_311, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_828, c_6848])).
% 34.52/24.04  tff(c_150, plain, (![B_67, A_68]: (r1_tarski(k10_relat_1(B_67, A_68), k1_relat_1(B_67)) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 34.52/24.04  tff(c_159, plain, (![A_42, A_68]: (r1_tarski(k10_relat_1(k6_relat_1(A_42), A_68), A_42) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_150])).
% 34.52/24.04  tff(c_164, plain, (![A_42, A_68]: (r1_tarski(k10_relat_1(k6_relat_1(A_42), A_68), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_159])).
% 34.52/24.04  tff(c_6939, plain, (![A_42, A_68]: (r1_tarski(k3_xboole_0(A_42, A_68), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_6897, c_164])).
% 34.52/24.04  tff(c_1160, plain, (![A_145, B_146]: (k10_relat_1(A_145, k1_relat_1(B_146))=k1_relat_1(k5_relat_1(A_145, B_146)) | ~v1_relat_1(B_146) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_90])).
% 34.52/24.04  tff(c_1240, plain, (![A_145, A_42]: (k1_relat_1(k5_relat_1(A_145, k6_relat_1(A_42)))=k10_relat_1(A_145, A_42) | ~v1_relat_1(k6_relat_1(A_42)) | ~v1_relat_1(A_145))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1160])).
% 34.52/24.04  tff(c_1310, plain, (![A_149, A_150]: (k1_relat_1(k5_relat_1(A_149, k6_relat_1(A_150)))=k10_relat_1(A_149, A_150) | ~v1_relat_1(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1240])).
% 34.52/24.04  tff(c_1351, plain, (![A_150, A_45]: (k1_relat_1(k7_relat_1(k6_relat_1(A_150), A_45))=k10_relat_1(k6_relat_1(A_45), A_150) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(k6_relat_1(A_150)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1310])).
% 34.52/24.04  tff(c_1357, plain, (![A_150, A_45]: (k1_relat_1(k7_relat_1(k6_relat_1(A_150), A_45))=k10_relat_1(k6_relat_1(A_45), A_150))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_1351])).
% 34.52/24.04  tff(c_6932, plain, (![A_150, A_45]: (k1_relat_1(k7_relat_1(k6_relat_1(A_150), A_45))=k3_xboole_0(A_45, A_150))), inference(demodulation, [status(thm), theory('equality')], [c_6897, c_1357])).
% 34.52/24.04  tff(c_915, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_52, c_868])).
% 34.52/24.04  tff(c_48, plain, (![A_49, C_51, B_50]: (k3_xboole_0(A_49, k10_relat_1(C_51, B_50))=k10_relat_1(k7_relat_1(C_51, A_49), B_50) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_112])).
% 34.52/24.04  tff(c_208, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(k7_relat_1(B_77, A_78)), k1_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_98])).
% 34.52/24.04  tff(c_213, plain, (![A_42, A_78]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_42), A_78)), A_42) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_208])).
% 34.52/24.04  tff(c_216, plain, (![A_42, A_78]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_42), A_78)), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_213])).
% 34.52/24.04  tff(c_1452, plain, (![A_155, A_156]: (r1_tarski(k10_relat_1(k6_relat_1(A_155), A_156), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_216])).
% 34.52/24.04  tff(c_864, plain, (![A_97, A_42]: (k3_xboole_0(A_97, A_42)=A_42 | ~r1_tarski(A_42, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_853])).
% 34.52/24.04  tff(c_2536, plain, (![A_201, A_202]: (k3_xboole_0(A_201, k10_relat_1(k6_relat_1(A_202), A_201))=k10_relat_1(k6_relat_1(A_202), A_201))), inference(resolution, [status(thm)], [c_1452, c_864])).
% 34.52/24.04  tff(c_2583, plain, (![A_202, B_50]: (k10_relat_1(k7_relat_1(k6_relat_1(A_202), B_50), B_50)=k10_relat_1(k6_relat_1(A_202), B_50) | ~v1_relat_1(k6_relat_1(A_202)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2536])).
% 34.52/24.04  tff(c_2608, plain, (![A_202, B_50]: (k10_relat_1(k7_relat_1(k6_relat_1(A_202), B_50), B_50)=k10_relat_1(k6_relat_1(A_202), B_50))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2583])).
% 34.52/24.04  tff(c_6919, plain, (![A_202, B_50]: (k10_relat_1(k7_relat_1(k6_relat_1(A_202), B_50), B_50)=k3_xboole_0(A_202, B_50))), inference(demodulation, [status(thm), theory('equality')], [c_6897, c_2608])).
% 34.52/24.04  tff(c_6940, plain, (![A_314, A_315]: (k10_relat_1(k6_relat_1(A_314), A_315)=k3_xboole_0(A_314, A_315))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_828, c_6848])).
% 34.52/24.04  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 34.52/24.04  tff(c_811, plain, (![C_129, B_130]: (k10_relat_1(k7_relat_1(C_129, k10_relat_1(C_129, B_130)), B_130)=k10_relat_1(C_129, B_130) | ~v1_relat_1(C_129))), inference(superposition, [status(thm), theory('equality')], [c_804, c_2])).
% 34.52/24.04  tff(c_6949, plain, (![A_314, A_315]: (k10_relat_1(k7_relat_1(k6_relat_1(A_314), k3_xboole_0(A_314, A_315)), A_315)=k10_relat_1(k6_relat_1(A_314), A_315) | ~v1_relat_1(k6_relat_1(A_314)))), inference(superposition, [status(thm), theory('equality')], [c_6940, c_811])).
% 34.52/24.04  tff(c_22601, plain, (![A_682, A_683]: (k10_relat_1(k7_relat_1(k6_relat_1(A_682), k3_xboole_0(A_682, A_683)), A_683)=k3_xboole_0(A_682, A_683))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6897, c_6949])).
% 34.52/24.04  tff(c_22744, plain, (k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_1'), '#skF_1')=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_915, c_22601])).
% 34.52/24.04  tff(c_22803, plain, (k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_1'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_22744])).
% 34.52/24.04  tff(c_30, plain, (![B_33, A_32]: (r1_tarski(k10_relat_1(B_33, A_32), k1_relat_1(B_33)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 34.52/24.04  tff(c_176, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.52/24.04  tff(c_186, plain, (![B_33, A_32]: (k10_relat_1(B_33, A_32)=k1_relat_1(B_33) | ~r1_tarski(k1_relat_1(B_33), k10_relat_1(B_33, A_32)) | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_30, c_176])).
% 34.52/24.04  tff(c_22856, plain, (k10_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_1'), '#skF_1')=k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_1')) | ~r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_1')), '#skF_1') | ~v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22803, c_186])).
% 34.52/24.04  tff(c_22907, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1' | ~v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6939, c_6932, c_915, c_6919, c_6932, c_22856])).
% 34.52/24.04  tff(c_33309, plain, (~v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_1'))), inference(splitLeft, [status(thm)], [c_22907])).
% 34.52/24.04  tff(c_33315, plain, (~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_205, c_33309])).
% 34.52/24.04  tff(c_33321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_33315])).
% 34.52/24.04  tff(c_33322, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_22907])).
% 34.52/24.04  tff(c_6962, plain, (![A_314, A_49, A_315]: (k10_relat_1(k7_relat_1(k6_relat_1(A_314), A_49), A_315)=k3_xboole_0(A_49, k3_xboole_0(A_314, A_315)) | ~v1_relat_1(k6_relat_1(A_314)))), inference(superposition, [status(thm), theory('equality')], [c_6940, c_48])).
% 34.52/24.04  tff(c_7003, plain, (![A_314, A_49, A_315]: (k10_relat_1(k7_relat_1(k6_relat_1(A_314), A_49), A_315)=k3_xboole_0(A_49, k3_xboole_0(A_314, A_315)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6962])).
% 34.52/24.04  tff(c_9257, plain, (![A_393, A_394, B_395]: (k3_xboole_0(A_393, k1_relat_1(k5_relat_1(A_394, B_395)))=k10_relat_1(k7_relat_1(A_394, A_393), k1_relat_1(B_395)) | ~v1_relat_1(A_394) | ~v1_relat_1(B_395) | ~v1_relat_1(A_394))), inference(superposition, [status(thm), theory('equality')], [c_1160, c_48])).
% 34.52/24.04  tff(c_9377, plain, (![A_45, A_393, B_46]: (k10_relat_1(k7_relat_1(k6_relat_1(A_45), A_393), k1_relat_1(B_46))=k3_xboole_0(A_393, k1_relat_1(k7_relat_1(B_46, A_45))) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(B_46) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_44, c_9257])).
% 34.52/24.04  tff(c_9391, plain, (![A_45, A_393, B_46]: (k10_relat_1(k7_relat_1(k6_relat_1(A_45), A_393), k1_relat_1(B_46))=k3_xboole_0(A_393, k1_relat_1(k7_relat_1(B_46, A_45))) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_9377])).
% 34.52/24.04  tff(c_26905, plain, (![A_393, A_45, B_46]: (k3_xboole_0(A_393, k3_xboole_0(A_45, k1_relat_1(B_46)))=k3_xboole_0(A_393, k1_relat_1(k7_relat_1(B_46, A_45))) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_7003, c_9391])).
% 34.52/24.04  tff(c_33377, plain, (![A_393]: (k3_xboole_0(A_393, k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0(A_393, '#skF_1') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_33322, c_26905])).
% 34.52/24.04  tff(c_33784, plain, (![A_841]: (k3_xboole_0(A_841, k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0(A_841, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_33377])).
% 34.52/24.04  tff(c_1363, plain, (![A_78, A_42]: (r1_tarski(k10_relat_1(k6_relat_1(A_78), A_42), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_216])).
% 34.52/24.04  tff(c_6931, plain, (![A_78, A_42]: (r1_tarski(k3_xboole_0(A_78, A_42), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_6897, c_1363])).
% 34.52/24.04  tff(c_34443, plain, (![A_842]: (r1_tarski(k3_xboole_0(A_842, '#skF_1'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_33784, c_6931])).
% 34.52/24.04  tff(c_34471, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_910, c_34443])).
% 34.52/24.04  tff(c_34497, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34471])).
% 34.52/24.04  tff(c_34535, plain, (k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_34497, c_864])).
% 34.52/24.04  tff(c_34335, plain, (k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1')=k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_33784])).
% 34.52/24.04  tff(c_35165, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34535, c_34335])).
% 34.52/24.04  tff(c_35294, plain, (![A_32]: (r1_tarski(k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_32), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_35165, c_30])).
% 34.52/24.04  tff(c_43601, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_35294])).
% 34.52/24.04  tff(c_43604, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_205, c_43601])).
% 34.52/24.04  tff(c_43608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_43604])).
% 34.52/24.04  tff(c_43610, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_35294])).
% 34.52/24.04  tff(c_364, plain, (![B_96]: (k7_relat_1(B_96, k1_relat_1(B_96))=B_96 | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_8, c_341])).
% 34.52/24.04  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.52/24.04  tff(c_8481, plain, (![B_367, A_368]: (k1_relat_1(k7_relat_1(B_367, A_368))=k1_relat_1(B_367) | ~r1_tarski(k1_relat_1(B_367), k1_relat_1(k7_relat_1(B_367, A_368))) | ~v1_relat_1(B_367))), inference(resolution, [status(thm)], [c_208, c_4])).
% 34.52/24.04  tff(c_8522, plain, (![B_96]: (k1_relat_1(k7_relat_1(B_96, k1_relat_1(B_96)))=k1_relat_1(B_96) | ~r1_tarski(k1_relat_1(B_96), k1_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_364, c_8481])).
% 34.52/24.04  tff(c_8541, plain, (![B_96]: (k1_relat_1(k7_relat_1(B_96, k1_relat_1(B_96)))=k1_relat_1(B_96) | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8522])).
% 34.52/24.04  tff(c_35234, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_35165, c_8541])).
% 34.52/24.04  tff(c_35313, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_35165, c_35234])).
% 34.52/24.04  tff(c_45472, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_43610, c_35313])).
% 34.52/24.04  tff(c_26906, plain, (![A_739, A_740, B_741]: (k3_xboole_0(A_739, k3_xboole_0(A_740, k1_relat_1(B_741)))=k3_xboole_0(A_739, k1_relat_1(k7_relat_1(B_741, A_740))) | ~v1_relat_1(B_741))), inference(demodulation, [status(thm), theory('equality')], [c_7003, c_9391])).
% 34.52/24.04  tff(c_7082, plain, (![A_318, A_319]: (r1_tarski(k3_xboole_0(A_318, A_319), A_318))), inference(demodulation, [status(thm), theory('equality')], [c_6897, c_164])).
% 34.52/24.04  tff(c_7136, plain, (![A_318, A_319]: (k3_xboole_0(A_318, k3_xboole_0(A_318, A_319))=k3_xboole_0(A_318, A_319))), inference(resolution, [status(thm)], [c_7082, c_864])).
% 34.52/24.04  tff(c_106584, plain, (![A_1402, B_1403]: (k3_xboole_0(A_1402, k1_relat_1(k7_relat_1(B_1403, A_1402)))=k3_xboole_0(A_1402, k1_relat_1(B_1403)) | ~v1_relat_1(B_1403))), inference(superposition, [status(thm), theory('equality')], [c_26906, c_7136])).
% 34.52/24.04  tff(c_107796, plain, (![A_1404, B_1405]: (r1_tarski(k3_xboole_0(A_1404, k1_relat_1(B_1405)), k1_relat_1(k7_relat_1(B_1405, A_1404))) | ~v1_relat_1(B_1405))), inference(superposition, [status(thm), theory('equality')], [c_106584, c_6931])).
% 34.52/24.04  tff(c_108015, plain, (![B_1406]: (r1_tarski(k1_relat_1(B_1406), k1_relat_1(k7_relat_1(B_1406, k1_relat_1(B_1406)))) | ~v1_relat_1(B_1406))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107796])).
% 34.52/24.04  tff(c_46, plain, (![B_48, A_47]: (k7_relat_1(B_48, A_47)=B_48 | ~r1_tarski(k1_relat_1(B_48), A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_108])).
% 34.52/24.04  tff(c_109922, plain, (![B_1417]: (k7_relat_1(B_1417, k1_relat_1(k7_relat_1(B_1417, k1_relat_1(B_1417))))=B_1417 | ~v1_relat_1(B_1417))), inference(resolution, [status(thm)], [c_108015, c_46])).
% 34.52/24.04  tff(c_110148, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')))=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_35165, c_109922])).
% 34.52/24.04  tff(c_110230, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_43610, c_45472, c_110148])).
% 34.52/24.04  tff(c_32, plain, (![A_34]: (k10_relat_1(A_34, k2_relat_1(A_34))=k1_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_76])).
% 34.52/24.04  tff(c_820, plain, (![A_34, A_128]: (k10_relat_1(k7_relat_1(A_34, A_128), k2_relat_1(A_34))=k3_xboole_0(A_128, k1_relat_1(A_34)) | ~v1_relat_1(A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_32, c_804])).
% 34.52/24.04  tff(c_110376, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_110230, c_820])).
% 34.52/24.04  tff(c_110490, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_43610, c_43610, c_2, c_35165, c_110376])).
% 34.52/24.04  tff(c_6660, plain, (![A_311, B_312, A_313]: (k10_relat_1(k6_relat_1(A_311), k10_relat_1(B_312, A_313))=k1_relat_1(k6_relat_1(A_311)) | ~r1_tarski(k1_relat_1(k6_relat_1(A_311)), k10_relat_1(k7_relat_1(B_312, A_311), A_313)) | ~v1_relat_1(k6_relat_1(A_311)) | ~v1_relat_1(B_312))), inference(superposition, [status(thm), theory('equality')], [c_6619, c_186])).
% 34.52/24.04  tff(c_6864, plain, (![A_311, B_312, A_313]: (k10_relat_1(k6_relat_1(A_311), k10_relat_1(B_312, A_313))=A_311 | ~r1_tarski(A_311, k10_relat_1(k7_relat_1(B_312, A_311), A_313)) | ~v1_relat_1(B_312))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38, c_38, c_6660])).
% 34.52/24.04  tff(c_32767, plain, (![A_311, B_312, A_313]: (k3_xboole_0(A_311, k10_relat_1(B_312, A_313))=A_311 | ~r1_tarski(A_311, k10_relat_1(k7_relat_1(B_312, A_311), A_313)) | ~v1_relat_1(B_312))), inference(demodulation, [status(thm), theory('equality')], [c_6897, c_6864])).
% 34.52/24.04  tff(c_113230, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_110490, c_32767])).
% 34.52/24.04  tff(c_113369, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8, c_113230])).
% 34.52/24.04  tff(c_10272, plain, (![B_429, C_430]: (k10_relat_1(B_429, k10_relat_1(C_430, k2_relat_1(k5_relat_1(B_429, C_430))))=k1_relat_1(k5_relat_1(B_429, C_430)) | ~v1_relat_1(k5_relat_1(B_429, C_430)) | ~v1_relat_1(C_430) | ~v1_relat_1(B_429))), inference(superposition, [status(thm), theory('equality')], [c_2059, c_32])).
% 34.52/24.04  tff(c_10344, plain, (![A_45, B_46]: (k10_relat_1(k6_relat_1(A_45), k10_relat_1(B_46, k2_relat_1(k7_relat_1(B_46, A_45))))=k1_relat_1(k5_relat_1(k6_relat_1(A_45), B_46)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_45), B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_44, c_10272])).
% 34.52/24.04  tff(c_10355, plain, (![A_45, B_46]: (k3_xboole_0(A_45, k10_relat_1(B_46, k2_relat_1(k7_relat_1(B_46, A_45))))=k1_relat_1(k5_relat_1(k6_relat_1(A_45), B_46)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_45), B_46)) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6897, c_10344])).
% 34.52/24.04  tff(c_113865, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1' | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_113369, c_10355])).
% 34.52/24.04  tff(c_114230, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1' | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_113865])).
% 34.52/24.04  tff(c_129789, plain, (~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_114230])).
% 34.52/24.04  tff(c_129792, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44, c_129789])).
% 34.52/24.04  tff(c_129798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_43610, c_129792])).
% 34.52/24.04  tff(c_129800, plain, (v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_114230])).
% 34.52/24.04  tff(c_126, plain, (![A_63]: (k9_relat_1(A_63, k1_relat_1(A_63))=k2_relat_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 34.52/24.04  tff(c_135, plain, (![A_42]: (k9_relat_1(k6_relat_1(A_42), A_42)=k2_relat_1(k6_relat_1(A_42)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_126])).
% 34.52/24.04  tff(c_139, plain, (![A_42]: (k9_relat_1(k6_relat_1(A_42), A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_40, c_135])).
% 34.52/24.04  tff(c_129799, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_114230])).
% 34.52/24.04  tff(c_2454, plain, (![B_196, C_197, A_198]: (k9_relat_1(k5_relat_1(B_196, C_197), A_198)=k9_relat_1(C_197, k9_relat_1(B_196, A_198)) | ~v1_relat_1(C_197) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_68])).
% 34.52/24.04  tff(c_26, plain, (![A_27]: (k9_relat_1(A_27, k1_relat_1(A_27))=k2_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 34.52/24.04  tff(c_2461, plain, (![C_197, B_196]: (k9_relat_1(C_197, k9_relat_1(B_196, k1_relat_1(k5_relat_1(B_196, C_197))))=k2_relat_1(k5_relat_1(B_196, C_197)) | ~v1_relat_1(k5_relat_1(B_196, C_197)) | ~v1_relat_1(C_197) | ~v1_relat_1(B_196))), inference(superposition, [status(thm), theory('equality')], [c_2454, c_26])).
% 34.52/24.04  tff(c_130184, plain, (k9_relat_1('#skF_2', k9_relat_1(k6_relat_1('#skF_1'), '#skF_1'))=k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')) | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_129799, c_2461])).
% 34.52/24.04  tff(c_130350, plain, (k2_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_54, c_129800, c_139, c_130184])).
% 34.52/24.04  tff(c_130421, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44, c_130350])).
% 34.52/24.04  tff(c_130439, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_130421])).
% 34.52/24.04  tff(c_7018, plain, (![A_316, A_317]: (r1_tarski(k3_xboole_0(A_316, A_317), A_317))), inference(demodulation, [status(thm), theory('equality')], [c_6897, c_1363])).
% 34.52/24.04  tff(c_7063, plain, (![C_51, A_49, B_50]: (r1_tarski(k10_relat_1(k7_relat_1(C_51, A_49), B_50), k10_relat_1(C_51, B_50)) | ~v1_relat_1(C_51))), inference(superposition, [status(thm), theory('equality')], [c_48, c_7018])).
% 34.52/24.04  tff(c_113251, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_110490, c_7063])).
% 34.52/24.04  tff(c_113383, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_113251])).
% 34.52/24.04  tff(c_130446, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_130439, c_113383])).
% 34.52/24.04  tff(c_130449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_130446])).
% 34.52/24.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.52/24.04  
% 34.52/24.04  Inference rules
% 34.52/24.04  ----------------------
% 34.52/24.04  #Ref     : 0
% 34.52/24.04  #Sup     : 32642
% 34.52/24.04  #Fact    : 0
% 34.52/24.04  #Define  : 0
% 34.52/24.04  #Split   : 5
% 34.52/24.04  #Chain   : 0
% 34.52/24.04  #Close   : 0
% 34.52/24.04  
% 34.52/24.04  Ordering : KBO
% 34.52/24.04  
% 34.52/24.04  Simplification rules
% 34.52/24.04  ----------------------
% 34.52/24.04  #Subsume      : 7692
% 34.52/24.04  #Demod        : 13145
% 34.52/24.04  #Tautology    : 7366
% 34.52/24.04  #SimpNegUnit  : 2
% 34.52/24.04  #BackRed      : 70
% 34.52/24.04  
% 34.52/24.04  #Partial instantiations: 0
% 34.52/24.04  #Strategies tried      : 1
% 34.52/24.04  
% 34.52/24.04  Timing (in seconds)
% 34.52/24.04  ----------------------
% 34.52/24.05  Preprocessing        : 0.36
% 34.52/24.05  Parsing              : 0.20
% 34.52/24.05  CNF conversion       : 0.02
% 34.52/24.05  Main loop            : 22.82
% 34.52/24.05  Inferencing          : 2.54
% 34.52/24.05  Reduction            : 9.25
% 34.52/24.05  Demodulation         : 8.13
% 34.52/24.05  BG Simplification    : 0.34
% 34.52/24.05  Subsumption          : 9.60
% 34.52/24.05  Abstraction          : 0.48
% 34.52/24.05  MUC search           : 0.00
% 34.52/24.05  Cooper               : 0.00
% 34.52/24.05  Total                : 23.24
% 34.52/24.05  Index Insertion      : 0.00
% 34.52/24.05  Index Deletion       : 0.00
% 34.52/24.05  Index Matching       : 0.00
% 34.52/24.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
