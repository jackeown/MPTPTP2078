%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:46 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 6.29s
% Verified   : 
% Statistics : Number of formulae       :  133 (2423 expanded)
%              Number of leaves         :   40 ( 858 expanded)
%              Depth                    :   26
%              Number of atoms          :  222 (4504 expanded)
%              Number of equality atoms :   85 (1639 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_122,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | k4_xboole_0(A_59,B_60) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_50])).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k7_relat_1(A_23,B_24))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    ! [A_35] : k1_relat_1(k6_relat_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    ! [A_35] : k2_relat_1(k6_relat_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_424,plain,(
    ! [B_99,A_100] :
      ( k5_relat_1(B_99,k6_relat_1(A_100)) = B_99
      | ~ r1_tarski(k2_relat_1(B_99),A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_435,plain,(
    ! [A_35,A_100] :
      ( k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_100)) = k6_relat_1(A_35)
      | ~ r1_tarski(A_35,A_100)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_424])).

tff(c_443,plain,(
    ! [A_35,A_100] :
      ( k5_relat_1(k6_relat_1(A_35),k6_relat_1(A_100)) = k6_relat_1(A_35)
      | ~ r1_tarski(A_35,A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_435])).

tff(c_745,plain,(
    ! [A_124,B_125] :
      ( k10_relat_1(A_124,k1_relat_1(B_125)) = k1_relat_1(k5_relat_1(A_124,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_781,plain,(
    ! [A_124,A_35] :
      ( k1_relat_1(k5_relat_1(A_124,k6_relat_1(A_35))) = k10_relat_1(A_124,A_35)
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_745])).

tff(c_893,plain,(
    ! [A_128,A_129] :
      ( k1_relat_1(k5_relat_1(A_128,k6_relat_1(A_129))) = k10_relat_1(A_128,A_129)
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_781])).

tff(c_908,plain,(
    ! [A_35,A_100] :
      ( k10_relat_1(k6_relat_1(A_35),A_100) = k1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ r1_tarski(A_35,A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_893])).

tff(c_977,plain,(
    ! [A_131,A_132] :
      ( k10_relat_1(k6_relat_1(A_131),A_132) = A_131
      | ~ r1_tarski(A_131,A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_38,c_908])).

tff(c_573,plain,(
    ! [A_110,A_111] :
      ( k5_relat_1(k6_relat_1(A_110),k6_relat_1(A_111)) = k6_relat_1(A_110)
      | ~ r1_tarski(A_110,A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_435])).

tff(c_587,plain,(
    ! [A_111,A_110] :
      ( k7_relat_1(k6_relat_1(A_111),A_110) = k6_relat_1(A_110)
      | ~ v1_relat_1(k6_relat_1(A_111))
      | ~ r1_tarski(A_110,A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_46])).

tff(c_629,plain,(
    ! [A_114,A_115] :
      ( k7_relat_1(k6_relat_1(A_114),A_115) = k6_relat_1(A_115)
      | ~ r1_tarski(A_115,A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_587])).

tff(c_189,plain,(
    ! [A_69] :
      ( k10_relat_1(A_69,k2_relat_1(A_69)) = k1_relat_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_198,plain,(
    ! [A_35] :
      ( k10_relat_1(k6_relat_1(A_35),A_35) = k1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_189])).

tff(c_202,plain,(
    ! [A_35] : k10_relat_1(k6_relat_1(A_35),A_35) = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_38,c_198])).

tff(c_516,plain,(
    ! [A_104,C_105,B_106] :
      ( k3_xboole_0(A_104,k10_relat_1(C_105,B_106)) = k10_relat_1(k7_relat_1(C_105,A_104),B_106)
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_528,plain,(
    ! [A_35,A_104] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_35),A_104),A_35) = k3_xboole_0(A_104,A_35)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_516])).

tff(c_535,plain,(
    ! [A_35,A_104] : k10_relat_1(k7_relat_1(k6_relat_1(A_35),A_104),A_35) = k3_xboole_0(A_104,A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_528])).

tff(c_635,plain,(
    ! [A_115,A_114] :
      ( k10_relat_1(k6_relat_1(A_115),A_114) = k3_xboole_0(A_115,A_114)
      | ~ r1_tarski(A_115,A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_535])).

tff(c_2071,plain,(
    ! [A_169,A_170] :
      ( k3_xboole_0(A_169,A_170) = A_169
      | ~ r1_tarski(A_169,A_170)
      | ~ r1_tarski(A_169,A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_635])).

tff(c_2091,plain,
    ( k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_2071])).

tff(c_2109,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2091])).

tff(c_203,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_214,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_70,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_203])).

tff(c_927,plain,(
    ! [B_130] :
      ( k5_relat_1(B_130,k6_relat_1(k1_relat_1('#skF_2'))) = B_130
      | ~ v1_relat_1(B_130)
      | ~ r1_tarski(k2_relat_1(B_130),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_214,c_424])).

tff(c_960,plain,(
    ! [A_40] :
      ( k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),A_40) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(A_40)),'#skF_1')
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_927])).

tff(c_1814,plain,(
    ! [A_163] :
      ( k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')),A_163) = k6_relat_1(A_163)
      | ~ r1_tarski(A_163,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_40,c_26,c_960])).

tff(c_918,plain,(
    ! [A_129,A_40] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_129),A_40)) = k10_relat_1(k6_relat_1(A_40),A_129)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_893])).

tff(c_926,plain,(
    ! [A_129,A_40] : k1_relat_1(k7_relat_1(k6_relat_1(A_129),A_40)) = k10_relat_1(k6_relat_1(A_40),A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_918])).

tff(c_1826,plain,(
    ! [A_163] :
      ( k10_relat_1(k6_relat_1(A_163),k1_relat_1('#skF_2')) = k1_relat_1(k6_relat_1(A_163))
      | ~ r1_tarski(A_163,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_926])).

tff(c_1868,plain,(
    ! [A_163] :
      ( k10_relat_1(k6_relat_1(A_163),k1_relat_1('#skF_2')) = A_163
      | ~ r1_tarski(A_163,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1826])).

tff(c_84,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_1034,plain,(
    ! [A_133,A_134] : k1_relat_1(k7_relat_1(k6_relat_1(A_133),A_134)) = k10_relat_1(k6_relat_1(A_134),A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_918])).

tff(c_44,plain,(
    ! [B_39,A_38] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_39,A_38)),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1052,plain,(
    ! [A_134,A_133] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_134),A_133),A_134)
      | ~ v1_relat_1(k6_relat_1(A_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_44])).

tff(c_1068,plain,(
    ! [A_134,A_133] : r1_tarski(k10_relat_1(k6_relat_1(A_134),A_133),A_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1052])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_225,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_74,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_203])).

tff(c_14,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_396,plain,(
    ! [A_96,A_97] :
      ( r1_tarski(A_96,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_96,A_97)
      | ~ r1_tarski(A_97,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_225,c_14])).

tff(c_2932,plain,(
    ! [A_197,B_198] :
      ( r1_tarski(A_197,k1_relat_1('#skF_2'))
      | ~ r1_tarski(B_198,'#skF_1')
      | k4_xboole_0(A_197,B_198) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_396])).

tff(c_3892,plain,(
    ! [A_225,A_226] :
      ( r1_tarski(A_225,k1_relat_1('#skF_2'))
      | k4_xboole_0(A_225,k10_relat_1(k6_relat_1('#skF_1'),A_226)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1068,c_2932])).

tff(c_3965,plain,(
    ! [A_226] : r1_tarski(k10_relat_1(k6_relat_1('#skF_1'),A_226),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_3892])).

tff(c_3966,plain,(
    ! [A_227] : r1_tarski(k10_relat_1(k6_relat_1('#skF_1'),A_227),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_3892])).

tff(c_987,plain,(
    ! [A_131,A_132] :
      ( k3_xboole_0(A_131,A_132) = A_131
      | ~ r1_tarski(A_131,A_132)
      | ~ r1_tarski(A_131,A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_635])).

tff(c_3970,plain,(
    ! [A_227] :
      ( k3_xboole_0(k10_relat_1(k6_relat_1('#skF_1'),A_227),k1_relat_1('#skF_2')) = k10_relat_1(k6_relat_1('#skF_1'),A_227)
      | ~ r1_tarski(k10_relat_1(k6_relat_1('#skF_1'),A_227),k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3966,c_987])).

tff(c_5574,plain,(
    ! [A_260] : k3_xboole_0(k10_relat_1(k6_relat_1('#skF_1'),A_260),k1_relat_1('#skF_2')) = k10_relat_1(k6_relat_1('#skF_1'),A_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3965,c_3970])).

tff(c_5624,plain,
    ( k10_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1868,c_5574])).

tff(c_5679,plain,(
    k10_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2109,c_5624])).

tff(c_36,plain,(
    ! [A_32,B_34] :
      ( k10_relat_1(A_32,k1_relat_1(B_34)) = k1_relat_1(k5_relat_1(A_32,B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5761,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5679,c_36])).

tff(c_5818,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54,c_5761])).

tff(c_5914,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_5818])).

tff(c_5934,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5914])).

tff(c_763,plain,(
    ! [B_125] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_125)),B_125)) = k1_relat_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_125))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_202])).

tff(c_1515,plain,(
    ! [B_156] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_156)),B_156)) = k1_relat_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_763])).

tff(c_2969,plain,(
    ! [B_199] :
      ( k1_relat_1(k7_relat_1(B_199,k1_relat_1(B_199))) = k1_relat_1(B_199)
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(B_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1515])).

tff(c_168,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [B_39,A_38] :
      ( k1_relat_1(k7_relat_1(B_39,A_38)) = A_38
      | ~ r1_tarski(A_38,k1_relat_1(k7_relat_1(B_39,A_38)))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_44,c_168])).

tff(c_2978,plain,(
    ! [B_199] :
      ( k1_relat_1(k7_relat_1(B_199,k1_relat_1(B_199))) = k1_relat_1(B_199)
      | ~ r1_tarski(k1_relat_1(B_199),k1_relat_1(B_199))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(B_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2969,c_177])).

tff(c_3051,plain,(
    ! [B_199] :
      ( k1_relat_1(k7_relat_1(B_199,k1_relat_1(B_199))) = k1_relat_1(B_199)
      | ~ v1_relat_1(B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2978])).

tff(c_5949,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5934,c_3051])).

tff(c_5987,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5934,c_5949])).

tff(c_6706,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5987])).

tff(c_6709,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_6706])).

tff(c_6713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6709])).

tff(c_6715,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5987])).

tff(c_1178,plain,(
    ! [A_139,C_140,B_141] :
      ( k9_relat_1(k7_relat_1(A_139,C_140),B_141) = k9_relat_1(A_139,B_141)
      | ~ r1_tarski(B_141,C_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_relat_1(A_25)) = k2_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1185,plain,(
    ! [A_139,C_140] :
      ( k9_relat_1(A_139,k1_relat_1(k7_relat_1(A_139,C_140))) = k2_relat_1(k7_relat_1(A_139,C_140))
      | ~ v1_relat_1(k7_relat_1(A_139,C_140))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(A_139,C_140)),C_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_30])).

tff(c_5943,plain,
    ( k9_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5934,c_1185])).

tff(c_5984,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_5934,c_5943])).

tff(c_7204,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6715,c_5984])).

tff(c_34,plain,(
    ! [A_31] :
      ( k10_relat_1(A_31,k2_relat_1(A_31)) = k1_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7217,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7204,c_34])).

tff(c_7227,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6715,c_5934,c_7217])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_522,plain,(
    ! [A_104,C_105,B_106] :
      ( k5_xboole_0(A_104,k10_relat_1(k7_relat_1(C_105,A_104),B_106)) = k4_xboole_0(A_104,k10_relat_1(C_105,B_106))
      | ~ v1_relat_1(C_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_12])).

tff(c_7232,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7227,c_522])).

tff(c_7239,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16,c_7232])).

tff(c_7241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_7239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:17:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.23  
% 6.29/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.23  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.29/2.23  
% 6.29/2.23  %Foreground sorts:
% 6.29/2.23  
% 6.29/2.23  
% 6.29/2.23  %Background operators:
% 6.29/2.23  
% 6.29/2.23  
% 6.29/2.23  %Foreground operators:
% 6.29/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.29/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.29/2.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.29/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.29/2.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.29/2.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.29/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.29/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.29/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.29/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.29/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.29/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.29/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.29/2.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.29/2.23  tff('#skF_1', type, '#skF_1': $i).
% 6.29/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.29/2.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.29/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.29/2.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.29/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.29/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.29/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.29/2.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.29/2.23  
% 6.29/2.25  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.29/2.25  tff(f_110, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 6.29/2.25  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.29/2.25  tff(f_59, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.29/2.25  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.29/2.25  tff(f_55, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.29/2.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.29/2.25  tff(f_85, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.29/2.25  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 6.29/2.25  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 6.29/2.25  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 6.29/2.25  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 6.29/2.25  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.29/2.25  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 6.29/2.25  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 6.29/2.25  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 6.29/2.25  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.29/2.25  tff(c_122, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | k4_xboole_0(A_59, B_60)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.29/2.25  tff(c_50, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.29/2.25  tff(c_129, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_50])).
% 6.29/2.25  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.29/2.25  tff(c_16, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.29/2.25  tff(c_28, plain, (![A_23, B_24]: (v1_relat_1(k7_relat_1(A_23, B_24)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.29/2.25  tff(c_46, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.29/2.25  tff(c_26, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.29/2.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.29/2.25  tff(c_52, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.29/2.25  tff(c_38, plain, (![A_35]: (k1_relat_1(k6_relat_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.29/2.25  tff(c_40, plain, (![A_35]: (k2_relat_1(k6_relat_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.29/2.25  tff(c_424, plain, (![B_99, A_100]: (k5_relat_1(B_99, k6_relat_1(A_100))=B_99 | ~r1_tarski(k2_relat_1(B_99), A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.29/2.25  tff(c_435, plain, (![A_35, A_100]: (k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_100))=k6_relat_1(A_35) | ~r1_tarski(A_35, A_100) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_424])).
% 6.29/2.25  tff(c_443, plain, (![A_35, A_100]: (k5_relat_1(k6_relat_1(A_35), k6_relat_1(A_100))=k6_relat_1(A_35) | ~r1_tarski(A_35, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_435])).
% 6.29/2.25  tff(c_745, plain, (![A_124, B_125]: (k10_relat_1(A_124, k1_relat_1(B_125))=k1_relat_1(k5_relat_1(A_124, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.29/2.25  tff(c_781, plain, (![A_124, A_35]: (k1_relat_1(k5_relat_1(A_124, k6_relat_1(A_35)))=k10_relat_1(A_124, A_35) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_38, c_745])).
% 6.29/2.25  tff(c_893, plain, (![A_128, A_129]: (k1_relat_1(k5_relat_1(A_128, k6_relat_1(A_129)))=k10_relat_1(A_128, A_129) | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_781])).
% 6.29/2.25  tff(c_908, plain, (![A_35, A_100]: (k10_relat_1(k6_relat_1(A_35), A_100)=k1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_35)) | ~r1_tarski(A_35, A_100))), inference(superposition, [status(thm), theory('equality')], [c_443, c_893])).
% 6.29/2.25  tff(c_977, plain, (![A_131, A_132]: (k10_relat_1(k6_relat_1(A_131), A_132)=A_131 | ~r1_tarski(A_131, A_132))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_38, c_908])).
% 6.29/2.25  tff(c_573, plain, (![A_110, A_111]: (k5_relat_1(k6_relat_1(A_110), k6_relat_1(A_111))=k6_relat_1(A_110) | ~r1_tarski(A_110, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_435])).
% 6.29/2.25  tff(c_587, plain, (![A_111, A_110]: (k7_relat_1(k6_relat_1(A_111), A_110)=k6_relat_1(A_110) | ~v1_relat_1(k6_relat_1(A_111)) | ~r1_tarski(A_110, A_111))), inference(superposition, [status(thm), theory('equality')], [c_573, c_46])).
% 6.29/2.25  tff(c_629, plain, (![A_114, A_115]: (k7_relat_1(k6_relat_1(A_114), A_115)=k6_relat_1(A_115) | ~r1_tarski(A_115, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_587])).
% 6.29/2.25  tff(c_189, plain, (![A_69]: (k10_relat_1(A_69, k2_relat_1(A_69))=k1_relat_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.29/2.25  tff(c_198, plain, (![A_35]: (k10_relat_1(k6_relat_1(A_35), A_35)=k1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_189])).
% 6.29/2.25  tff(c_202, plain, (![A_35]: (k10_relat_1(k6_relat_1(A_35), A_35)=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_38, c_198])).
% 6.29/2.25  tff(c_516, plain, (![A_104, C_105, B_106]: (k3_xboole_0(A_104, k10_relat_1(C_105, B_106))=k10_relat_1(k7_relat_1(C_105, A_104), B_106) | ~v1_relat_1(C_105))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.29/2.25  tff(c_528, plain, (![A_35, A_104]: (k10_relat_1(k7_relat_1(k6_relat_1(A_35), A_104), A_35)=k3_xboole_0(A_104, A_35) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_516])).
% 6.29/2.25  tff(c_535, plain, (![A_35, A_104]: (k10_relat_1(k7_relat_1(k6_relat_1(A_35), A_104), A_35)=k3_xboole_0(A_104, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_528])).
% 6.29/2.25  tff(c_635, plain, (![A_115, A_114]: (k10_relat_1(k6_relat_1(A_115), A_114)=k3_xboole_0(A_115, A_114) | ~r1_tarski(A_115, A_114))), inference(superposition, [status(thm), theory('equality')], [c_629, c_535])).
% 6.29/2.25  tff(c_2071, plain, (![A_169, A_170]: (k3_xboole_0(A_169, A_170)=A_169 | ~r1_tarski(A_169, A_170) | ~r1_tarski(A_169, A_170))), inference(superposition, [status(thm), theory('equality')], [c_977, c_635])).
% 6.29/2.25  tff(c_2091, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_2071])).
% 6.29/2.25  tff(c_2109, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2091])).
% 6.29/2.25  tff(c_203, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.29/2.25  tff(c_214, plain, (![A_70]: (r1_tarski(A_70, k1_relat_1('#skF_2')) | ~r1_tarski(A_70, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_203])).
% 6.29/2.25  tff(c_927, plain, (![B_130]: (k5_relat_1(B_130, k6_relat_1(k1_relat_1('#skF_2')))=B_130 | ~v1_relat_1(B_130) | ~r1_tarski(k2_relat_1(B_130), '#skF_1'))), inference(resolution, [status(thm)], [c_214, c_424])).
% 6.29/2.25  tff(c_960, plain, (![A_40]: (k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), A_40)=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_40)) | ~r1_tarski(k2_relat_1(k6_relat_1(A_40)), '#skF_1') | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_46, c_927])).
% 6.29/2.25  tff(c_1814, plain, (![A_163]: (k7_relat_1(k6_relat_1(k1_relat_1('#skF_2')), A_163)=k6_relat_1(A_163) | ~r1_tarski(A_163, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_40, c_26, c_960])).
% 6.29/2.25  tff(c_918, plain, (![A_129, A_40]: (k1_relat_1(k7_relat_1(k6_relat_1(A_129), A_40))=k10_relat_1(k6_relat_1(A_40), A_129) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_129)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_893])).
% 6.29/2.25  tff(c_926, plain, (![A_129, A_40]: (k1_relat_1(k7_relat_1(k6_relat_1(A_129), A_40))=k10_relat_1(k6_relat_1(A_40), A_129))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_918])).
% 6.29/2.25  tff(c_1826, plain, (![A_163]: (k10_relat_1(k6_relat_1(A_163), k1_relat_1('#skF_2'))=k1_relat_1(k6_relat_1(A_163)) | ~r1_tarski(A_163, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1814, c_926])).
% 6.29/2.25  tff(c_1868, plain, (![A_163]: (k10_relat_1(k6_relat_1(A_163), k1_relat_1('#skF_2'))=A_163 | ~r1_tarski(A_163, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1826])).
% 6.29/2.25  tff(c_84, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.29/2.25  tff(c_92, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_84])).
% 6.29/2.25  tff(c_1034, plain, (![A_133, A_134]: (k1_relat_1(k7_relat_1(k6_relat_1(A_133), A_134))=k10_relat_1(k6_relat_1(A_134), A_133))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_918])).
% 6.29/2.25  tff(c_44, plain, (![B_39, A_38]: (r1_tarski(k1_relat_1(k7_relat_1(B_39, A_38)), A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.29/2.25  tff(c_1052, plain, (![A_134, A_133]: (r1_tarski(k10_relat_1(k6_relat_1(A_134), A_133), A_134) | ~v1_relat_1(k6_relat_1(A_133)))), inference(superposition, [status(thm), theory('equality')], [c_1034, c_44])).
% 6.29/2.25  tff(c_1068, plain, (![A_134, A_133]: (r1_tarski(k10_relat_1(k6_relat_1(A_134), A_133), A_134))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1052])).
% 6.29/2.25  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.29/2.25  tff(c_225, plain, (![A_74]: (r1_tarski(A_74, k1_relat_1('#skF_2')) | ~r1_tarski(A_74, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_203])).
% 6.29/2.25  tff(c_14, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.29/2.25  tff(c_396, plain, (![A_96, A_97]: (r1_tarski(A_96, k1_relat_1('#skF_2')) | ~r1_tarski(A_96, A_97) | ~r1_tarski(A_97, '#skF_1'))), inference(resolution, [status(thm)], [c_225, c_14])).
% 6.29/2.25  tff(c_2932, plain, (![A_197, B_198]: (r1_tarski(A_197, k1_relat_1('#skF_2')) | ~r1_tarski(B_198, '#skF_1') | k4_xboole_0(A_197, B_198)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_396])).
% 6.29/2.25  tff(c_3892, plain, (![A_225, A_226]: (r1_tarski(A_225, k1_relat_1('#skF_2')) | k4_xboole_0(A_225, k10_relat_1(k6_relat_1('#skF_1'), A_226))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1068, c_2932])).
% 6.29/2.25  tff(c_3965, plain, (![A_226]: (r1_tarski(k10_relat_1(k6_relat_1('#skF_1'), A_226), k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_3892])).
% 6.29/2.25  tff(c_3966, plain, (![A_227]: (r1_tarski(k10_relat_1(k6_relat_1('#skF_1'), A_227), k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_3892])).
% 6.29/2.25  tff(c_987, plain, (![A_131, A_132]: (k3_xboole_0(A_131, A_132)=A_131 | ~r1_tarski(A_131, A_132) | ~r1_tarski(A_131, A_132))), inference(superposition, [status(thm), theory('equality')], [c_977, c_635])).
% 6.29/2.25  tff(c_3970, plain, (![A_227]: (k3_xboole_0(k10_relat_1(k6_relat_1('#skF_1'), A_227), k1_relat_1('#skF_2'))=k10_relat_1(k6_relat_1('#skF_1'), A_227) | ~r1_tarski(k10_relat_1(k6_relat_1('#skF_1'), A_227), k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_3966, c_987])).
% 6.29/2.25  tff(c_5574, plain, (![A_260]: (k3_xboole_0(k10_relat_1(k6_relat_1('#skF_1'), A_260), k1_relat_1('#skF_2'))=k10_relat_1(k6_relat_1('#skF_1'), A_260))), inference(demodulation, [status(thm), theory('equality')], [c_3965, c_3970])).
% 6.29/2.25  tff(c_5624, plain, (k10_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k3_xboole_0('#skF_1', k1_relat_1('#skF_2')) | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1868, c_5574])).
% 6.29/2.25  tff(c_5679, plain, (k10_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2109, c_5624])).
% 6.29/2.25  tff(c_36, plain, (![A_32, B_34]: (k10_relat_1(A_32, k1_relat_1(B_34))=k1_relat_1(k5_relat_1(A_32, B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.29/2.25  tff(c_5761, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5679, c_36])).
% 6.29/2.25  tff(c_5818, plain, (k1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54, c_5761])).
% 6.29/2.25  tff(c_5914, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46, c_5818])).
% 6.29/2.25  tff(c_5934, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5914])).
% 6.29/2.25  tff(c_763, plain, (![B_125]: (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_125)), B_125))=k1_relat_1(B_125) | ~v1_relat_1(B_125) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_125))))), inference(superposition, [status(thm), theory('equality')], [c_745, c_202])).
% 6.29/2.25  tff(c_1515, plain, (![B_156]: (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(B_156)), B_156))=k1_relat_1(B_156) | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_763])).
% 6.29/2.25  tff(c_2969, plain, (![B_199]: (k1_relat_1(k7_relat_1(B_199, k1_relat_1(B_199)))=k1_relat_1(B_199) | ~v1_relat_1(B_199) | ~v1_relat_1(B_199))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1515])).
% 6.29/2.25  tff(c_168, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.29/2.25  tff(c_177, plain, (![B_39, A_38]: (k1_relat_1(k7_relat_1(B_39, A_38))=A_38 | ~r1_tarski(A_38, k1_relat_1(k7_relat_1(B_39, A_38))) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_44, c_168])).
% 6.29/2.25  tff(c_2978, plain, (![B_199]: (k1_relat_1(k7_relat_1(B_199, k1_relat_1(B_199)))=k1_relat_1(B_199) | ~r1_tarski(k1_relat_1(B_199), k1_relat_1(B_199)) | ~v1_relat_1(B_199) | ~v1_relat_1(B_199) | ~v1_relat_1(B_199))), inference(superposition, [status(thm), theory('equality')], [c_2969, c_177])).
% 6.29/2.25  tff(c_3051, plain, (![B_199]: (k1_relat_1(k7_relat_1(B_199, k1_relat_1(B_199)))=k1_relat_1(B_199) | ~v1_relat_1(B_199))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2978])).
% 6.29/2.25  tff(c_5949, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5934, c_3051])).
% 6.29/2.25  tff(c_5987, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5934, c_5949])).
% 6.29/2.25  tff(c_6706, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_5987])).
% 6.29/2.25  tff(c_6709, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_6706])).
% 6.29/2.25  tff(c_6713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_6709])).
% 6.29/2.25  tff(c_6715, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_5987])).
% 6.29/2.25  tff(c_1178, plain, (![A_139, C_140, B_141]: (k9_relat_1(k7_relat_1(A_139, C_140), B_141)=k9_relat_1(A_139, B_141) | ~r1_tarski(B_141, C_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.29/2.25  tff(c_30, plain, (![A_25]: (k9_relat_1(A_25, k1_relat_1(A_25))=k2_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.29/2.25  tff(c_1185, plain, (![A_139, C_140]: (k9_relat_1(A_139, k1_relat_1(k7_relat_1(A_139, C_140)))=k2_relat_1(k7_relat_1(A_139, C_140)) | ~v1_relat_1(k7_relat_1(A_139, C_140)) | ~r1_tarski(k1_relat_1(k7_relat_1(A_139, C_140)), C_140) | ~v1_relat_1(A_139))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_30])).
% 6.29/2.25  tff(c_5943, plain, (k9_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5934, c_1185])).
% 6.29/2.25  tff(c_5984, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_5934, c_5943])).
% 6.29/2.25  tff(c_7204, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6715, c_5984])).
% 6.29/2.25  tff(c_34, plain, (![A_31]: (k10_relat_1(A_31, k2_relat_1(A_31))=k1_relat_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.29/2.25  tff(c_7217, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7204, c_34])).
% 6.29/2.25  tff(c_7227, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6715, c_5934, c_7217])).
% 6.29/2.25  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.29/2.25  tff(c_522, plain, (![A_104, C_105, B_106]: (k5_xboole_0(A_104, k10_relat_1(k7_relat_1(C_105, A_104), B_106))=k4_xboole_0(A_104, k10_relat_1(C_105, B_106)) | ~v1_relat_1(C_105))), inference(superposition, [status(thm), theory('equality')], [c_516, c_12])).
% 6.29/2.25  tff(c_7232, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7227, c_522])).
% 6.29/2.25  tff(c_7239, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16, c_7232])).
% 6.29/2.25  tff(c_7241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_7239])).
% 6.29/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.25  
% 6.29/2.25  Inference rules
% 6.29/2.25  ----------------------
% 6.29/2.25  #Ref     : 0
% 6.29/2.25  #Sup     : 1615
% 6.29/2.25  #Fact    : 0
% 6.29/2.25  #Define  : 0
% 6.29/2.25  #Split   : 2
% 6.29/2.25  #Chain   : 0
% 6.29/2.25  #Close   : 0
% 6.29/2.25  
% 6.29/2.25  Ordering : KBO
% 6.29/2.25  
% 6.29/2.25  Simplification rules
% 6.29/2.25  ----------------------
% 6.29/2.25  #Subsume      : 289
% 6.29/2.25  #Demod        : 1295
% 6.29/2.25  #Tautology    : 676
% 6.29/2.25  #SimpNegUnit  : 1
% 6.29/2.25  #BackRed      : 0
% 6.29/2.25  
% 6.29/2.25  #Partial instantiations: 0
% 6.29/2.25  #Strategies tried      : 1
% 6.29/2.25  
% 6.29/2.25  Timing (in seconds)
% 6.29/2.25  ----------------------
% 6.29/2.25  Preprocessing        : 0.33
% 6.29/2.25  Parsing              : 0.18
% 6.29/2.25  CNF conversion       : 0.02
% 6.29/2.25  Main loop            : 1.16
% 6.29/2.25  Inferencing          : 0.37
% 6.29/2.25  Reduction            : 0.42
% 6.29/2.25  Demodulation         : 0.31
% 6.29/2.25  BG Simplification    : 0.04
% 6.29/2.26  Subsumption          : 0.25
% 6.29/2.26  Abstraction          : 0.06
% 6.29/2.26  MUC search           : 0.00
% 6.29/2.26  Cooper               : 0.00
% 6.29/2.26  Total                : 1.53
% 6.29/2.26  Index Insertion      : 0.00
% 6.29/2.26  Index Deletion       : 0.00
% 6.29/2.26  Index Matching       : 0.00
% 6.29/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
