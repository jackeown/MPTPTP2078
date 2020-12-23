%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:47 EST 2020

% Result     : Theorem 8.67s
% Output     : CNFRefutation 8.67s
% Verified   : 
% Statistics : Number of formulae       :  139 (4300 expanded)
%              Number of leaves         :   38 (1547 expanded)
%              Depth                    :   29
%              Number of atoms          :  244 (7980 expanded)
%              Number of equality atoms :   70 (2939 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_121,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_114,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(k7_relat_1(B,A),A) = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

tff(c_52,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k7_relat_1(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    ! [A_44] : v1_relat_1(k6_relat_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [A_40] : k2_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_166,plain,(
    ! [A_71] :
      ( k10_relat_1(A_71,k2_relat_1(A_71)) = k1_relat_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_182,plain,(
    ! [A_40] :
      ( k10_relat_1(k6_relat_1(A_40),A_40) = k1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_166])).

tff(c_189,plain,(
    ! [A_40] : k10_relat_1(k6_relat_1(A_40),A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_182])).

tff(c_98,plain,(
    ! [A_61] :
      ( k7_relat_1(A_61,k1_relat_1(A_61)) = A_61
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_110,plain,(
    ! [A_40] :
      ( k7_relat_1(k6_relat_1(A_40),A_40) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_98])).

tff(c_114,plain,(
    ! [A_40] : k7_relat_1(k6_relat_1(A_40),A_40) = k6_relat_1(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_110])).

tff(c_1056,plain,(
    ! [C_146,A_147,B_148] :
      ( k7_relat_1(k7_relat_1(C_146,A_147),B_148) = k7_relat_1(C_146,A_147)
      | ~ r1_tarski(A_147,B_148)
      | ~ v1_relat_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1097,plain,(
    ! [A_40,B_148] :
      ( k7_relat_1(k6_relat_1(A_40),B_148) = k7_relat_1(k6_relat_1(A_40),A_40)
      | ~ r1_tarski(A_40,B_148)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1056])).

tff(c_1118,plain,(
    ! [A_149,B_150] :
      ( k7_relat_1(k6_relat_1(A_149),B_150) = k6_relat_1(A_149)
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_114,c_1097])).

tff(c_698,plain,(
    ! [A_129,C_130,B_131] :
      ( k3_xboole_0(A_129,k10_relat_1(C_130,B_131)) = k10_relat_1(k7_relat_1(C_130,A_129),B_131)
      | ~ v1_relat_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_735,plain,(
    ! [A_40,A_129] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_40),A_129),A_40) = k3_xboole_0(A_129,A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_698])).

tff(c_744,plain,(
    ! [A_40,A_129] : k10_relat_1(k7_relat_1(k6_relat_1(A_40),A_129),A_40) = k3_xboole_0(A_129,A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_735])).

tff(c_1127,plain,(
    ! [B_150,A_149] :
      ( k3_xboole_0(B_150,A_149) = k10_relat_1(k6_relat_1(A_149),A_149)
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_744])).

tff(c_1188,plain,(
    ! [B_151,A_152] :
      ( k3_xboole_0(B_151,A_152) = A_152
      | ~ r1_tarski(A_152,B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_1127])).

tff(c_1235,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_1188])).

tff(c_217,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(A_76,C_77)
      | ~ r1_tarski(B_78,C_77)
      | ~ r1_tarski(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_231,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_76,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_217])).

tff(c_42,plain,(
    ! [A_43] :
      ( k7_relat_1(A_43,k1_relat_1(A_43)) = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6223,plain,(
    ! [A_308,B_309] :
      ( k7_relat_1(A_308,k1_relat_1(A_308)) = k7_relat_1(A_308,B_309)
      | ~ r1_tarski(k1_relat_1(A_308),B_309)
      | ~ v1_relat_1(A_308)
      | ~ v1_relat_1(A_308) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1056])).

tff(c_6411,plain,(
    ! [A_312] :
      ( k7_relat_1(A_312,k1_relat_1(A_312)) = k7_relat_1(A_312,k1_relat_1('#skF_2'))
      | ~ v1_relat_1(A_312)
      | ~ r1_tarski(k1_relat_1(A_312),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_231,c_6223])).

tff(c_6440,plain,(
    ! [A_40] :
      ( k7_relat_1(k6_relat_1(A_40),k1_relat_1(k6_relat_1(A_40))) = k7_relat_1(k6_relat_1(A_40),k1_relat_1('#skF_2'))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_40,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6411])).

tff(c_6451,plain,(
    ! [A_40] :
      ( k7_relat_1(k6_relat_1(A_40),k1_relat_1('#skF_2')) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_114,c_36,c_6440])).

tff(c_2041,plain,(
    ! [A_183,B_184] :
      ( k7_relat_1(A_183,k1_relat_1(k7_relat_1(B_184,k1_relat_1(A_183)))) = k7_relat_1(A_183,k1_relat_1(B_184))
      | ~ v1_relat_1(B_184)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_42,A_41)),A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7647,plain,(
    ! [A_335,B_336] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_335,k1_relat_1(B_336))),k1_relat_1(k7_relat_1(B_336,k1_relat_1(A_335))))
      | ~ v1_relat_1(A_335)
      | ~ v1_relat_1(B_336)
      | ~ v1_relat_1(A_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2041,c_40])).

tff(c_7666,plain,(
    ! [A_40] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_40)),k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(k6_relat_1(A_40)))))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_40,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6451,c_7647])).

tff(c_7827,plain,(
    ! [A_337] :
      ( r1_tarski(A_337,k1_relat_1(k7_relat_1('#skF_2',A_337)))
      | ~ r1_tarski(A_337,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56,c_44,c_36,c_36,c_7666])).

tff(c_146,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [B_42,A_41] :
      ( k1_relat_1(k7_relat_1(B_42,A_41)) = A_41
      | ~ r1_tarski(A_41,k1_relat_1(k7_relat_1(B_42,A_41)))
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_40,c_146])).

tff(c_7842,plain,(
    ! [A_337] :
      ( k1_relat_1(k7_relat_1('#skF_2',A_337)) = A_337
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_337,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_7827,c_157])).

tff(c_7877,plain,(
    ! [A_337] :
      ( k1_relat_1(k7_relat_1('#skF_2',A_337)) = A_337
      | ~ r1_tarski(A_337,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7842])).

tff(c_1232,plain,(
    ! [A_76] :
      ( k3_xboole_0(k1_relat_1('#skF_2'),A_76) = A_76
      | ~ r1_tarski(A_76,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_231,c_1188])).

tff(c_50,plain,(
    ! [B_49,A_48] : k5_relat_1(k6_relat_1(B_49),k6_relat_1(A_48)) = k6_relat_1(k3_xboole_0(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_448,plain,(
    ! [A_103,B_104] :
      ( k10_relat_1(A_103,k1_relat_1(B_104)) = k1_relat_1(k5_relat_1(A_103,B_104))
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_129,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k10_relat_1(B_63,A_64),k1_relat_1(B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,(
    ! [A_40,A_64] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_40),A_64),A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_129])).

tff(c_134,plain,(
    ! [A_40,A_64] : r1_tarski(k10_relat_1(k6_relat_1(A_40),A_64),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_132])).

tff(c_475,plain,(
    ! [A_40,B_104] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_40),B_104)),A_40)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_134])).

tff(c_507,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_105),B_106)),A_105)
      | ~ v1_relat_1(B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_475])).

tff(c_520,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_48,B_49))),B_49)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_507])).

tff(c_526,plain,(
    ! [A_48,B_49] : r1_tarski(k3_xboole_0(A_48,B_49),B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_520])).

tff(c_7669,plain,(
    ! [A_40] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(k6_relat_1(A_40)))),k1_relat_1(k6_relat_1(A_40)))
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_40,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6451,c_7647])).

tff(c_8062,plain,(
    ! [A_339] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_339)),A_339)
      | ~ r1_tarski(A_339,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_56,c_36,c_36,c_7669])).

tff(c_527,plain,(
    ! [A_107,B_108] : r1_tarski(k3_xboole_0(A_107,B_108),B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_520])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_583,plain,(
    ! [A_114,B_115,A_116] :
      ( r1_tarski(A_114,B_115)
      | ~ r1_tarski(A_114,k3_xboole_0(A_116,B_115)) ) ),
    inference(resolution,[status(thm)],[c_527,c_8])).

tff(c_620,plain,(
    ! [A_117,A_118,B_119] : r1_tarski(k3_xboole_0(A_117,k3_xboole_0(A_118,B_119)),B_119) ),
    inference(resolution,[status(thm)],[c_526,c_583])).

tff(c_233,plain,(
    ! [A_79] :
      ( r1_tarski(A_79,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_79,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_217])).

tff(c_238,plain,(
    ! [A_3,A_79] :
      ( r1_tarski(A_3,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_3,A_79)
      | ~ r1_tarski(A_79,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_233,c_8])).

tff(c_636,plain,(
    ! [A_117,A_118,B_119] :
      ( r1_tarski(k3_xboole_0(A_117,k3_xboole_0(A_118,B_119)),k1_relat_1('#skF_2'))
      | ~ r1_tarski(B_119,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_620,c_238])).

tff(c_1241,plain,(
    ! [A_117] :
      ( r1_tarski(k3_xboole_0(A_117,'#skF_1'),k1_relat_1('#skF_2'))
      | ~ r1_tarski('#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_636])).

tff(c_1354,plain,(
    ! [A_154] : r1_tarski(k3_xboole_0(A_154,'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1241])).

tff(c_1377,plain,(
    ! [A_3,A_154] :
      ( r1_tarski(A_3,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_3,k3_xboole_0(A_154,'#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1354,c_8])).

tff(c_8109,plain,(
    ! [A_154] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_2',k3_xboole_0(A_154,'#skF_1'))),k1_relat_1('#skF_2'))
      | ~ r1_tarski(k3_xboole_0(A_154,'#skF_1'),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8062,c_1377])).

tff(c_8216,plain,(
    ! [A_341] : r1_tarski(k1_relat_1(k7_relat_1('#skF_2',k3_xboole_0(A_341,'#skF_1'))),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_8109])).

tff(c_8244,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_8216])).

tff(c_8264,plain,(
    r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8244])).

tff(c_1164,plain,(
    ! [B_150,A_149] :
      ( k3_xboole_0(B_150,A_149) = A_149
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_1127])).

tff(c_8284,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_8264,c_1164])).

tff(c_10437,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7877,c_8284])).

tff(c_10467,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1235,c_10437])).

tff(c_3456,plain,(
    ! [B_236,A_237] :
      ( k1_relat_1(k7_relat_1(B_236,A_237)) = A_237
      | ~ r1_tarski(A_237,k1_relat_1(k7_relat_1(B_236,A_237)))
      | ~ v1_relat_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_40,c_146])).

tff(c_3478,plain,(
    ! [A_43] :
      ( k1_relat_1(k7_relat_1(A_43,k1_relat_1(A_43))) = k1_relat_1(A_43)
      | ~ r1_tarski(k1_relat_1(A_43),k1_relat_1(A_43))
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3456])).

tff(c_3485,plain,(
    ! [A_43] :
      ( k1_relat_1(k7_relat_1(A_43,k1_relat_1(A_43))) = k1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3478])).

tff(c_10536,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10467,c_3485])).

tff(c_10619,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10467,c_10536])).

tff(c_11612,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10619])).

tff(c_11615,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_11612])).

tff(c_11619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11615])).

tff(c_11621,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10619])).

tff(c_783,plain,(
    ! [A_135,A_136] : k10_relat_1(k7_relat_1(k6_relat_1(A_135),A_136),A_135) = k3_xboole_0(A_136,A_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_735])).

tff(c_809,plain,(
    ! [A_40] : k10_relat_1(k6_relat_1(A_40),A_40) = k3_xboole_0(A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_783])).

tff(c_817,plain,(
    ! [A_40] : k3_xboole_0(A_40,A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_809])).

tff(c_2127,plain,(
    ! [A_40,B_184] :
      ( k7_relat_1(k6_relat_1(A_40),k1_relat_1(k7_relat_1(B_184,A_40))) = k7_relat_1(k6_relat_1(A_40),k1_relat_1(B_184))
      | ~ v1_relat_1(B_184)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2041])).

tff(c_2148,plain,(
    ! [A_40,B_184] :
      ( k7_relat_1(k6_relat_1(A_40),k1_relat_1(k7_relat_1(B_184,A_40))) = k7_relat_1(k6_relat_1(A_40),k1_relat_1(B_184))
      | ~ v1_relat_1(B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2127])).

tff(c_10533,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k7_relat_1(k6_relat_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10467,c_2148])).

tff(c_10618,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_114,c_10533])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2079,plain,(
    ! [A_183,B_184] :
      ( k9_relat_1(A_183,k1_relat_1(k7_relat_1(B_184,k1_relat_1(A_183)))) = k2_relat_1(k7_relat_1(A_183,k1_relat_1(B_184)))
      | ~ v1_relat_1(A_183)
      | ~ v1_relat_1(B_184)
      | ~ v1_relat_1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2041,c_24])).

tff(c_10678,plain,
    ( k2_relat_1(k7_relat_1('#skF_2',k1_relat_1(k6_relat_1('#skF_1')))) = k9_relat_1('#skF_2',k1_relat_1(k6_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10618,c_2079])).

tff(c_10784,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_56,c_36,c_36,c_10678])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(k7_relat_1(B_20,A_19),A_19) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14363,plain,(
    ! [A_414,B_415] :
      ( k7_relat_1(k7_relat_1(A_414,k1_relat_1(B_415)),k1_relat_1(k7_relat_1(B_415,k1_relat_1(A_414)))) = k7_relat_1(A_414,k1_relat_1(k7_relat_1(B_415,k1_relat_1(A_414))))
      | ~ v1_relat_1(A_414)
      | ~ v1_relat_1(B_415)
      | ~ v1_relat_1(A_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2041,c_20])).

tff(c_14536,plain,
    ( k7_relat_1(k7_relat_1('#skF_2',k1_relat_1(k6_relat_1('#skF_1'))),k1_relat_1(k6_relat_1('#skF_1'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2'))))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10618,c_14363])).

tff(c_14688,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_56,c_36,c_36,c_36,c_10618,c_14536])).

tff(c_30,plain,(
    ! [A_33] :
      ( k10_relat_1(A_33,k2_relat_1(A_33)) = k1_relat_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_738,plain,(
    ! [A_33,A_129] :
      ( k10_relat_1(k7_relat_1(A_33,A_129),k2_relat_1(A_33)) = k3_xboole_0(A_129,k1_relat_1(A_33))
      | ~ v1_relat_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_698])).

tff(c_14773,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14688,c_738])).

tff(c_14857,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11621,c_11621,c_817,c_10467,c_10784,c_14773])).

tff(c_726,plain,(
    ! [C_130,A_129,B_131] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_130,A_129),B_131),k10_relat_1(C_130,B_131))
      | ~ v1_relat_1(C_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_526])).

tff(c_14988,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14857,c_726])).

tff(c_15033,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14988])).

tff(c_15035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_15033])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:35:23 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.67/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.08  
% 8.67/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.08  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.67/3.08  
% 8.67/3.08  %Foreground sorts:
% 8.67/3.08  
% 8.67/3.08  
% 8.67/3.08  %Background operators:
% 8.67/3.08  
% 8.67/3.08  
% 8.67/3.08  %Foreground operators:
% 8.67/3.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.67/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.67/3.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.67/3.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.67/3.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.67/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.67/3.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.67/3.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.67/3.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.67/3.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.67/3.08  tff('#skF_2', type, '#skF_2': $i).
% 8.67/3.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.67/3.08  tff('#skF_1', type, '#skF_1': $i).
% 8.67/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.67/3.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.67/3.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.67/3.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.67/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.67/3.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.67/3.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.67/3.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.67/3.08  
% 8.67/3.10  tff(f_121, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 8.67/3.10  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 8.67/3.10  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.67/3.10  tff(f_108, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.67/3.10  tff(f_96, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.67/3.10  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 8.67/3.10  tff(f_104, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 8.67/3.10  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 8.67/3.10  tff(f_112, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 8.67/3.10  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.67/3.10  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 8.67/3.10  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 8.67/3.10  tff(f_114, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 8.67/3.10  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 8.67/3.10  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 8.67/3.10  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.67/3.10  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(k7_relat_1(B, A), A) = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_relat_1)).
% 8.67/3.10  tff(c_52, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.67/3.10  tff(c_56, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.67/3.10  tff(c_18, plain, (![A_17, B_18]: (v1_relat_1(k7_relat_1(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.67/3.10  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.67/3.10  tff(c_54, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.67/3.10  tff(c_44, plain, (![A_44]: (v1_relat_1(k6_relat_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.67/3.10  tff(c_36, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.67/3.10  tff(c_38, plain, (![A_40]: (k2_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.67/3.10  tff(c_166, plain, (![A_71]: (k10_relat_1(A_71, k2_relat_1(A_71))=k1_relat_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.67/3.10  tff(c_182, plain, (![A_40]: (k10_relat_1(k6_relat_1(A_40), A_40)=k1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_166])).
% 8.67/3.10  tff(c_189, plain, (![A_40]: (k10_relat_1(k6_relat_1(A_40), A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_182])).
% 8.67/3.10  tff(c_98, plain, (![A_61]: (k7_relat_1(A_61, k1_relat_1(A_61))=A_61 | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.67/3.10  tff(c_110, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), A_40)=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_98])).
% 8.67/3.10  tff(c_114, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), A_40)=k6_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_110])).
% 8.67/3.10  tff(c_1056, plain, (![C_146, A_147, B_148]: (k7_relat_1(k7_relat_1(C_146, A_147), B_148)=k7_relat_1(C_146, A_147) | ~r1_tarski(A_147, B_148) | ~v1_relat_1(C_146))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.67/3.10  tff(c_1097, plain, (![A_40, B_148]: (k7_relat_1(k6_relat_1(A_40), B_148)=k7_relat_1(k6_relat_1(A_40), A_40) | ~r1_tarski(A_40, B_148) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_1056])).
% 8.67/3.10  tff(c_1118, plain, (![A_149, B_150]: (k7_relat_1(k6_relat_1(A_149), B_150)=k6_relat_1(A_149) | ~r1_tarski(A_149, B_150))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_114, c_1097])).
% 8.67/3.10  tff(c_698, plain, (![A_129, C_130, B_131]: (k3_xboole_0(A_129, k10_relat_1(C_130, B_131))=k10_relat_1(k7_relat_1(C_130, A_129), B_131) | ~v1_relat_1(C_130))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.67/3.10  tff(c_735, plain, (![A_40, A_129]: (k10_relat_1(k7_relat_1(k6_relat_1(A_40), A_129), A_40)=k3_xboole_0(A_129, A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_698])).
% 8.67/3.10  tff(c_744, plain, (![A_40, A_129]: (k10_relat_1(k7_relat_1(k6_relat_1(A_40), A_129), A_40)=k3_xboole_0(A_129, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_735])).
% 8.67/3.10  tff(c_1127, plain, (![B_150, A_149]: (k3_xboole_0(B_150, A_149)=k10_relat_1(k6_relat_1(A_149), A_149) | ~r1_tarski(A_149, B_150))), inference(superposition, [status(thm), theory('equality')], [c_1118, c_744])).
% 8.67/3.10  tff(c_1188, plain, (![B_151, A_152]: (k3_xboole_0(B_151, A_152)=A_152 | ~r1_tarski(A_152, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_1127])).
% 8.67/3.10  tff(c_1235, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_54, c_1188])).
% 8.67/3.10  tff(c_217, plain, (![A_76, C_77, B_78]: (r1_tarski(A_76, C_77) | ~r1_tarski(B_78, C_77) | ~r1_tarski(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.67/3.10  tff(c_231, plain, (![A_76]: (r1_tarski(A_76, k1_relat_1('#skF_2')) | ~r1_tarski(A_76, '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_217])).
% 8.67/3.10  tff(c_42, plain, (![A_43]: (k7_relat_1(A_43, k1_relat_1(A_43))=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.67/3.10  tff(c_6223, plain, (![A_308, B_309]: (k7_relat_1(A_308, k1_relat_1(A_308))=k7_relat_1(A_308, B_309) | ~r1_tarski(k1_relat_1(A_308), B_309) | ~v1_relat_1(A_308) | ~v1_relat_1(A_308))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1056])).
% 8.67/3.10  tff(c_6411, plain, (![A_312]: (k7_relat_1(A_312, k1_relat_1(A_312))=k7_relat_1(A_312, k1_relat_1('#skF_2')) | ~v1_relat_1(A_312) | ~r1_tarski(k1_relat_1(A_312), '#skF_1'))), inference(resolution, [status(thm)], [c_231, c_6223])).
% 8.67/3.10  tff(c_6440, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), k1_relat_1(k6_relat_1(A_40)))=k7_relat_1(k6_relat_1(A_40), k1_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_40, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_6411])).
% 8.67/3.10  tff(c_6451, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), k1_relat_1('#skF_2'))=k6_relat_1(A_40) | ~r1_tarski(A_40, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_114, c_36, c_6440])).
% 8.67/3.10  tff(c_2041, plain, (![A_183, B_184]: (k7_relat_1(A_183, k1_relat_1(k7_relat_1(B_184, k1_relat_1(A_183))))=k7_relat_1(A_183, k1_relat_1(B_184)) | ~v1_relat_1(B_184) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.67/3.10  tff(c_40, plain, (![B_42, A_41]: (r1_tarski(k1_relat_1(k7_relat_1(B_42, A_41)), A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.67/3.10  tff(c_7647, plain, (![A_335, B_336]: (r1_tarski(k1_relat_1(k7_relat_1(A_335, k1_relat_1(B_336))), k1_relat_1(k7_relat_1(B_336, k1_relat_1(A_335)))) | ~v1_relat_1(A_335) | ~v1_relat_1(B_336) | ~v1_relat_1(A_335))), inference(superposition, [status(thm), theory('equality')], [c_2041, c_40])).
% 8.67/3.10  tff(c_7666, plain, (![A_40]: (r1_tarski(k1_relat_1(k6_relat_1(A_40)), k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(k6_relat_1(A_40))))) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_40, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6451, c_7647])).
% 8.67/3.10  tff(c_7827, plain, (![A_337]: (r1_tarski(A_337, k1_relat_1(k7_relat_1('#skF_2', A_337))) | ~r1_tarski(A_337, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56, c_44, c_36, c_36, c_7666])).
% 8.67/3.10  tff(c_146, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.67/3.10  tff(c_157, plain, (![B_42, A_41]: (k1_relat_1(k7_relat_1(B_42, A_41))=A_41 | ~r1_tarski(A_41, k1_relat_1(k7_relat_1(B_42, A_41))) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_40, c_146])).
% 8.67/3.10  tff(c_7842, plain, (![A_337]: (k1_relat_1(k7_relat_1('#skF_2', A_337))=A_337 | ~v1_relat_1('#skF_2') | ~r1_tarski(A_337, '#skF_1'))), inference(resolution, [status(thm)], [c_7827, c_157])).
% 8.67/3.10  tff(c_7877, plain, (![A_337]: (k1_relat_1(k7_relat_1('#skF_2', A_337))=A_337 | ~r1_tarski(A_337, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_7842])).
% 8.67/3.10  tff(c_1232, plain, (![A_76]: (k3_xboole_0(k1_relat_1('#skF_2'), A_76)=A_76 | ~r1_tarski(A_76, '#skF_1'))), inference(resolution, [status(thm)], [c_231, c_1188])).
% 8.67/3.10  tff(c_50, plain, (![B_49, A_48]: (k5_relat_1(k6_relat_1(B_49), k6_relat_1(A_48))=k6_relat_1(k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.67/3.10  tff(c_448, plain, (![A_103, B_104]: (k10_relat_1(A_103, k1_relat_1(B_104))=k1_relat_1(k5_relat_1(A_103, B_104)) | ~v1_relat_1(B_104) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.67/3.10  tff(c_129, plain, (![B_63, A_64]: (r1_tarski(k10_relat_1(B_63, A_64), k1_relat_1(B_63)) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.67/3.10  tff(c_132, plain, (![A_40, A_64]: (r1_tarski(k10_relat_1(k6_relat_1(A_40), A_64), A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_129])).
% 8.67/3.10  tff(c_134, plain, (![A_40, A_64]: (r1_tarski(k10_relat_1(k6_relat_1(A_40), A_64), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_132])).
% 8.67/3.10  tff(c_475, plain, (![A_40, B_104]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_40), B_104)), A_40) | ~v1_relat_1(B_104) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_448, c_134])).
% 8.67/3.10  tff(c_507, plain, (![A_105, B_106]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_105), B_106)), A_105) | ~v1_relat_1(B_106))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_475])).
% 8.67/3.10  tff(c_520, plain, (![A_48, B_49]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_48, B_49))), B_49) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_507])).
% 8.67/3.10  tff(c_526, plain, (![A_48, B_49]: (r1_tarski(k3_xboole_0(A_48, B_49), B_49))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_520])).
% 8.67/3.10  tff(c_7669, plain, (![A_40]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(k6_relat_1(A_40)))), k1_relat_1(k6_relat_1(A_40))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1('#skF_2') | ~r1_tarski(A_40, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6451, c_7647])).
% 8.67/3.10  tff(c_8062, plain, (![A_339]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_339)), A_339) | ~r1_tarski(A_339, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44, c_56, c_36, c_36, c_7669])).
% 8.67/3.10  tff(c_527, plain, (![A_107, B_108]: (r1_tarski(k3_xboole_0(A_107, B_108), B_108))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_520])).
% 8.67/3.10  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.67/3.10  tff(c_583, plain, (![A_114, B_115, A_116]: (r1_tarski(A_114, B_115) | ~r1_tarski(A_114, k3_xboole_0(A_116, B_115)))), inference(resolution, [status(thm)], [c_527, c_8])).
% 8.67/3.10  tff(c_620, plain, (![A_117, A_118, B_119]: (r1_tarski(k3_xboole_0(A_117, k3_xboole_0(A_118, B_119)), B_119))), inference(resolution, [status(thm)], [c_526, c_583])).
% 8.67/3.10  tff(c_233, plain, (![A_79]: (r1_tarski(A_79, k1_relat_1('#skF_2')) | ~r1_tarski(A_79, '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_217])).
% 8.67/3.10  tff(c_238, plain, (![A_3, A_79]: (r1_tarski(A_3, k1_relat_1('#skF_2')) | ~r1_tarski(A_3, A_79) | ~r1_tarski(A_79, '#skF_1'))), inference(resolution, [status(thm)], [c_233, c_8])).
% 8.67/3.10  tff(c_636, plain, (![A_117, A_118, B_119]: (r1_tarski(k3_xboole_0(A_117, k3_xboole_0(A_118, B_119)), k1_relat_1('#skF_2')) | ~r1_tarski(B_119, '#skF_1'))), inference(resolution, [status(thm)], [c_620, c_238])).
% 8.67/3.10  tff(c_1241, plain, (![A_117]: (r1_tarski(k3_xboole_0(A_117, '#skF_1'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_636])).
% 8.67/3.10  tff(c_1354, plain, (![A_154]: (r1_tarski(k3_xboole_0(A_154, '#skF_1'), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1241])).
% 8.67/3.10  tff(c_1377, plain, (![A_3, A_154]: (r1_tarski(A_3, k1_relat_1('#skF_2')) | ~r1_tarski(A_3, k3_xboole_0(A_154, '#skF_1')))), inference(resolution, [status(thm)], [c_1354, c_8])).
% 8.67/3.10  tff(c_8109, plain, (![A_154]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', k3_xboole_0(A_154, '#skF_1'))), k1_relat_1('#skF_2')) | ~r1_tarski(k3_xboole_0(A_154, '#skF_1'), '#skF_1'))), inference(resolution, [status(thm)], [c_8062, c_1377])).
% 8.67/3.10  tff(c_8216, plain, (![A_341]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', k3_xboole_0(A_341, '#skF_1'))), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_8109])).
% 8.67/3.10  tff(c_8244, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1232, c_8216])).
% 8.67/3.10  tff(c_8264, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8244])).
% 8.67/3.10  tff(c_1164, plain, (![B_150, A_149]: (k3_xboole_0(B_150, A_149)=A_149 | ~r1_tarski(A_149, B_150))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_1127])).
% 8.67/3.10  tff(c_8284, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_8264, c_1164])).
% 8.67/3.10  tff(c_10437, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7877, c_8284])).
% 8.67/3.10  tff(c_10467, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1235, c_10437])).
% 8.67/3.10  tff(c_3456, plain, (![B_236, A_237]: (k1_relat_1(k7_relat_1(B_236, A_237))=A_237 | ~r1_tarski(A_237, k1_relat_1(k7_relat_1(B_236, A_237))) | ~v1_relat_1(B_236))), inference(resolution, [status(thm)], [c_40, c_146])).
% 8.67/3.10  tff(c_3478, plain, (![A_43]: (k1_relat_1(k7_relat_1(A_43, k1_relat_1(A_43)))=k1_relat_1(A_43) | ~r1_tarski(k1_relat_1(A_43), k1_relat_1(A_43)) | ~v1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3456])).
% 8.67/3.10  tff(c_3485, plain, (![A_43]: (k1_relat_1(k7_relat_1(A_43, k1_relat_1(A_43)))=k1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3478])).
% 8.67/3.10  tff(c_10536, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10467, c_3485])).
% 8.67/3.10  tff(c_10619, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10467, c_10536])).
% 8.67/3.10  tff(c_11612, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_10619])).
% 8.67/3.10  tff(c_11615, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_11612])).
% 8.67/3.10  tff(c_11619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_11615])).
% 8.67/3.10  tff(c_11621, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_10619])).
% 8.67/3.10  tff(c_783, plain, (![A_135, A_136]: (k10_relat_1(k7_relat_1(k6_relat_1(A_135), A_136), A_135)=k3_xboole_0(A_136, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_735])).
% 8.67/3.10  tff(c_809, plain, (![A_40]: (k10_relat_1(k6_relat_1(A_40), A_40)=k3_xboole_0(A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_114, c_783])).
% 8.67/3.10  tff(c_817, plain, (![A_40]: (k3_xboole_0(A_40, A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_189, c_809])).
% 8.67/3.10  tff(c_2127, plain, (![A_40, B_184]: (k7_relat_1(k6_relat_1(A_40), k1_relat_1(k7_relat_1(B_184, A_40)))=k7_relat_1(k6_relat_1(A_40), k1_relat_1(B_184)) | ~v1_relat_1(B_184) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2041])).
% 8.67/3.10  tff(c_2148, plain, (![A_40, B_184]: (k7_relat_1(k6_relat_1(A_40), k1_relat_1(k7_relat_1(B_184, A_40)))=k7_relat_1(k6_relat_1(A_40), k1_relat_1(B_184)) | ~v1_relat_1(B_184))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2127])).
% 8.67/3.10  tff(c_10533, plain, (k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k7_relat_1(k6_relat_1('#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10467, c_2148])).
% 8.67/3.10  tff(c_10618, plain, (k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_114, c_10533])).
% 8.67/3.10  tff(c_24, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.67/3.10  tff(c_2079, plain, (![A_183, B_184]: (k9_relat_1(A_183, k1_relat_1(k7_relat_1(B_184, k1_relat_1(A_183))))=k2_relat_1(k7_relat_1(A_183, k1_relat_1(B_184))) | ~v1_relat_1(A_183) | ~v1_relat_1(B_184) | ~v1_relat_1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_2041, c_24])).
% 8.67/3.10  tff(c_10678, plain, (k2_relat_1(k7_relat_1('#skF_2', k1_relat_1(k6_relat_1('#skF_1'))))=k9_relat_1('#skF_2', k1_relat_1(k6_relat_1('#skF_1'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10618, c_2079])).
% 8.67/3.10  tff(c_10784, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44, c_56, c_36, c_36, c_10678])).
% 8.67/3.10  tff(c_20, plain, (![B_20, A_19]: (k7_relat_1(k7_relat_1(B_20, A_19), A_19)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.67/3.10  tff(c_14363, plain, (![A_414, B_415]: (k7_relat_1(k7_relat_1(A_414, k1_relat_1(B_415)), k1_relat_1(k7_relat_1(B_415, k1_relat_1(A_414))))=k7_relat_1(A_414, k1_relat_1(k7_relat_1(B_415, k1_relat_1(A_414)))) | ~v1_relat_1(A_414) | ~v1_relat_1(B_415) | ~v1_relat_1(A_414))), inference(superposition, [status(thm), theory('equality')], [c_2041, c_20])).
% 8.67/3.10  tff(c_14536, plain, (k7_relat_1(k7_relat_1('#skF_2', k1_relat_1(k6_relat_1('#skF_1'))), k1_relat_1(k6_relat_1('#skF_1')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2')))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10618, c_14363])).
% 8.67/3.10  tff(c_14688, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44, c_56, c_36, c_36, c_36, c_10618, c_14536])).
% 8.67/3.10  tff(c_30, plain, (![A_33]: (k10_relat_1(A_33, k2_relat_1(A_33))=k1_relat_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.67/3.10  tff(c_738, plain, (![A_33, A_129]: (k10_relat_1(k7_relat_1(A_33, A_129), k2_relat_1(A_33))=k3_xboole_0(A_129, k1_relat_1(A_33)) | ~v1_relat_1(A_33) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_30, c_698])).
% 8.67/3.10  tff(c_14773, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14688, c_738])).
% 8.67/3.10  tff(c_14857, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11621, c_11621, c_817, c_10467, c_10784, c_14773])).
% 8.67/3.10  tff(c_726, plain, (![C_130, A_129, B_131]: (r1_tarski(k10_relat_1(k7_relat_1(C_130, A_129), B_131), k10_relat_1(C_130, B_131)) | ~v1_relat_1(C_130))), inference(superposition, [status(thm), theory('equality')], [c_698, c_526])).
% 8.67/3.10  tff(c_14988, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14857, c_726])).
% 8.67/3.10  tff(c_15033, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14988])).
% 8.67/3.10  tff(c_15035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_15033])).
% 8.67/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.10  
% 8.67/3.10  Inference rules
% 8.67/3.10  ----------------------
% 8.67/3.10  #Ref     : 0
% 8.67/3.10  #Sup     : 3550
% 8.67/3.10  #Fact    : 0
% 8.67/3.10  #Define  : 0
% 8.67/3.10  #Split   : 2
% 8.67/3.10  #Chain   : 0
% 8.67/3.10  #Close   : 0
% 8.67/3.10  
% 8.67/3.10  Ordering : KBO
% 8.67/3.10  
% 8.67/3.10  Simplification rules
% 8.67/3.10  ----------------------
% 8.67/3.10  #Subsume      : 802
% 8.67/3.10  #Demod        : 2889
% 8.67/3.10  #Tautology    : 1203
% 8.67/3.10  #SimpNegUnit  : 1
% 8.67/3.10  #BackRed      : 15
% 8.67/3.10  
% 8.67/3.10  #Partial instantiations: 0
% 8.67/3.10  #Strategies tried      : 1
% 8.67/3.10  
% 8.67/3.10  Timing (in seconds)
% 8.67/3.10  ----------------------
% 8.67/3.11  Preprocessing        : 0.33
% 8.67/3.11  Parsing              : 0.18
% 8.67/3.11  CNF conversion       : 0.02
% 8.67/3.11  Main loop            : 2.00
% 8.67/3.11  Inferencing          : 0.57
% 8.67/3.11  Reduction            : 0.73
% 8.67/3.11  Demodulation         : 0.57
% 8.67/3.11  BG Simplification    : 0.07
% 8.67/3.11  Subsumption          : 0.50
% 8.67/3.11  Abstraction          : 0.11
% 8.67/3.11  MUC search           : 0.00
% 8.67/3.11  Cooper               : 0.00
% 8.67/3.11  Total                : 2.38
% 8.67/3.11  Index Insertion      : 0.00
% 8.67/3.11  Index Deletion       : 0.00
% 8.67/3.11  Index Matching       : 0.00
% 8.67/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
