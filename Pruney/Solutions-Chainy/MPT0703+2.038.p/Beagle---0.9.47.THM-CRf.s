%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:13 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 297 expanded)
%              Number of leaves         :   40 ( 119 expanded)
%              Depth                    :   15
%              Number of atoms          :  133 ( 595 expanded)
%              Number of equality atoms :   35 ( 111 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k11_relat_1 > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_48,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_50,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_909,plain,(
    ! [B_104,A_105] :
      ( k9_relat_1(B_104,k10_relat_1(B_104,A_105)) = A_105
      | ~ r1_tarski(A_105,k2_relat_1(B_104))
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_923,plain,
    ( k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_2')) = '#skF_2'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_909])).

tff(c_936,plain,(
    k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_923])).

tff(c_52,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_118,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_128,plain,(
    k3_xboole_0(k10_relat_1('#skF_4','#skF_2'),k10_relat_1('#skF_4','#skF_3')) = k10_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_1389,plain,(
    ! [C_125,A_126,B_127] :
      ( r1_tarski(k9_relat_1(C_125,k3_xboole_0(A_126,k10_relat_1(C_125,B_127))),k3_xboole_0(k9_relat_1(C_125,A_126),B_127))
      | ~ v1_funct_1(C_125)
      | ~ v1_relat_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1436,plain,
    ( r1_tarski(k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_2')),k3_xboole_0(k9_relat_1('#skF_4',k10_relat_1('#skF_4','#skF_2')),'#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_1389])).

tff(c_1462,plain,(
    r1_tarski('#skF_2',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_936,c_936,c_1436])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_79,plain,(
    ! [A_46] :
      ( k7_relat_1(A_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    k7_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k7_relat_1(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_91,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_20])).

tff(c_95,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_91])).

tff(c_261,plain,(
    ! [A_57,B_58] :
      ( v1_funct_1(k7_relat_1(A_57,B_58))
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_267,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_261])).

tff(c_271,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_267])).

tff(c_28,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_104,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_28])).

tff(c_168,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_53,A_54)),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_184,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_168])).

tff(c_191,plain,(
    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_184])).

tff(c_12,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_203,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_12])).

tff(c_211,plain,(
    ! [A_55] :
      ( k9_relat_1(A_55,k1_relat_1(A_55)) = k2_relat_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_220,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_211])).

tff(c_224,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_104,c_220])).

tff(c_655,plain,(
    ! [B_92,A_93] :
      ( k7_relat_1(B_92,A_93) = B_92
      | ~ r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_668,plain,(
    ! [A_93] :
      ( k7_relat_1(k1_xboole_0,A_93) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_93)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_655])).

tff(c_680,plain,(
    ! [A_94] : k7_relat_1(k1_xboole_0,A_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_8,c_668])).

tff(c_26,plain,(
    ! [B_24,A_23] :
      ( k2_relat_1(k7_relat_1(B_24,A_23)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_696,plain,(
    ! [A_94] :
      ( k9_relat_1(k1_xboole_0,A_94) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_26])).

tff(c_726,plain,(
    ! [A_94] : k9_relat_1(k1_xboole_0,A_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_224,c_696])).

tff(c_1061,plain,(
    ! [A_110,B_111] :
      ( k3_xboole_0(A_110,k9_relat_1(B_111,k1_relat_1(B_111))) = k9_relat_1(B_111,k10_relat_1(B_111,A_110))
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1093,plain,(
    ! [A_110] :
      ( k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,A_110)) = k3_xboole_0(A_110,k9_relat_1(k1_xboole_0,k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_1061])).

tff(c_1103,plain,(
    ! [A_110] : k3_xboole_0(A_110,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_271,c_726,c_726,c_1093])).

tff(c_740,plain,(
    ! [A_95,B_96,C_97] : r1_tarski(k2_xboole_0(k3_xboole_0(A_95,B_96),k3_xboole_0(A_95,C_97)),k2_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_775,plain,(
    ! [A_95,A_8] : r1_tarski(k2_xboole_0(k3_xboole_0(A_95,k1_xboole_0),k3_xboole_0(A_95,A_8)),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_740])).

tff(c_1106,plain,(
    ! [A_95,A_8] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(A_95,A_8)),A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_775])).

tff(c_1133,plain,(
    ! [A_113,A_114] : r1_tarski(k3_xboole_0(A_113,A_114),A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1106])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1181,plain,(
    ! [A_3,A_114,A_113] :
      ( r1_tarski(A_3,A_114)
      | ~ r1_tarski(A_3,k3_xboole_0(A_113,A_114)) ) ),
    inference(resolution,[status(thm)],[c_1133,c_4])).

tff(c_1467,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1462,c_1181])).

tff(c_1481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k11_relat_1 > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.20/1.50  
% 3.20/1.50  %Foreground sorts:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Background operators:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Foreground operators:
% 3.20/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.20/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.50  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.20/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.20/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.50  
% 3.20/1.51  tff(f_135, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 3.20/1.51  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.20/1.51  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.20/1.51  tff(f_124, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 3.20/1.51  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.51  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.20/1.51  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 3.20/1.51  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.20/1.51  tff(f_104, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.20/1.51  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 3.20/1.51  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.20/1.51  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.20/1.51  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.20/1.51  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.20/1.51  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.20/1.51  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 3.20/1.51  tff(f_43, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.20/1.51  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.20/1.51  tff(c_48, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.20/1.51  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.20/1.51  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.20/1.51  tff(c_50, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.20/1.51  tff(c_909, plain, (![B_104, A_105]: (k9_relat_1(B_104, k10_relat_1(B_104, A_105))=A_105 | ~r1_tarski(A_105, k2_relat_1(B_104)) | ~v1_funct_1(B_104) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.20/1.51  tff(c_923, plain, (k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_2'))='#skF_2' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_909])).
% 3.20/1.51  tff(c_936, plain, (k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_923])).
% 3.20/1.51  tff(c_52, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.20/1.51  tff(c_118, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.51  tff(c_128, plain, (k3_xboole_0(k10_relat_1('#skF_4', '#skF_2'), k10_relat_1('#skF_4', '#skF_3'))=k10_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_118])).
% 3.20/1.51  tff(c_1389, plain, (![C_125, A_126, B_127]: (r1_tarski(k9_relat_1(C_125, k3_xboole_0(A_126, k10_relat_1(C_125, B_127))), k3_xboole_0(k9_relat_1(C_125, A_126), B_127)) | ~v1_funct_1(C_125) | ~v1_relat_1(C_125))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.20/1.51  tff(c_1436, plain, (r1_tarski(k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_4', k10_relat_1('#skF_4', '#skF_2')), '#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_128, c_1389])).
% 3.20/1.51  tff(c_1462, plain, (r1_tarski('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_936, c_936, c_1436])).
% 3.20/1.51  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.51  tff(c_142, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.51  tff(c_154, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_142])).
% 3.20/1.51  tff(c_79, plain, (![A_46]: (k7_relat_1(A_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.51  tff(c_87, plain, (k7_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_79])).
% 3.20/1.51  tff(c_20, plain, (![A_19, B_20]: (v1_relat_1(k7_relat_1(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.51  tff(c_91, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_87, c_20])).
% 3.20/1.51  tff(c_95, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_91])).
% 3.20/1.51  tff(c_261, plain, (![A_57, B_58]: (v1_funct_1(k7_relat_1(A_57, B_58)) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.51  tff(c_267, plain, (v1_funct_1(k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_87, c_261])).
% 3.20/1.51  tff(c_271, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_267])).
% 3.20/1.51  tff(c_28, plain, (![A_25]: (k9_relat_1(A_25, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.51  tff(c_104, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_28])).
% 3.20/1.51  tff(c_168, plain, (![B_53, A_54]: (r1_tarski(k1_relat_1(k7_relat_1(B_53, A_54)), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.20/1.51  tff(c_184, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_87, c_168])).
% 3.20/1.51  tff(c_191, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_184])).
% 3.20/1.51  tff(c_12, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.51  tff(c_203, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_191, c_12])).
% 3.20/1.51  tff(c_211, plain, (![A_55]: (k9_relat_1(A_55, k1_relat_1(A_55))=k2_relat_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.51  tff(c_220, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_203, c_211])).
% 3.20/1.51  tff(c_224, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_95, c_104, c_220])).
% 3.20/1.51  tff(c_655, plain, (![B_92, A_93]: (k7_relat_1(B_92, A_93)=B_92 | ~r1_tarski(k1_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.20/1.51  tff(c_668, plain, (![A_93]: (k7_relat_1(k1_xboole_0, A_93)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_93) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_203, c_655])).
% 3.20/1.51  tff(c_680, plain, (![A_94]: (k7_relat_1(k1_xboole_0, A_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_8, c_668])).
% 3.20/1.51  tff(c_26, plain, (![B_24, A_23]: (k2_relat_1(k7_relat_1(B_24, A_23))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.20/1.51  tff(c_696, plain, (![A_94]: (k9_relat_1(k1_xboole_0, A_94)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_680, c_26])).
% 3.20/1.51  tff(c_726, plain, (![A_94]: (k9_relat_1(k1_xboole_0, A_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_224, c_696])).
% 3.20/1.51  tff(c_1061, plain, (![A_110, B_111]: (k3_xboole_0(A_110, k9_relat_1(B_111, k1_relat_1(B_111)))=k9_relat_1(B_111, k10_relat_1(B_111, A_110)) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.20/1.51  tff(c_1093, plain, (![A_110]: (k9_relat_1(k1_xboole_0, k10_relat_1(k1_xboole_0, A_110))=k3_xboole_0(A_110, k9_relat_1(k1_xboole_0, k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_203, c_1061])).
% 3.20/1.51  tff(c_1103, plain, (![A_110]: (k3_xboole_0(A_110, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_271, c_726, c_726, c_1093])).
% 3.20/1.51  tff(c_740, plain, (![A_95, B_96, C_97]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_95, B_96), k3_xboole_0(A_95, C_97)), k2_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.51  tff(c_775, plain, (![A_95, A_8]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_95, k1_xboole_0), k3_xboole_0(A_95, A_8)), A_8))), inference(superposition, [status(thm), theory('equality')], [c_154, c_740])).
% 3.20/1.51  tff(c_1106, plain, (![A_95, A_8]: (r1_tarski(k2_xboole_0(k1_xboole_0, k3_xboole_0(A_95, A_8)), A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_775])).
% 3.20/1.51  tff(c_1133, plain, (![A_113, A_114]: (r1_tarski(k3_xboole_0(A_113, A_114), A_114))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1106])).
% 3.20/1.51  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.20/1.51  tff(c_1181, plain, (![A_3, A_114, A_113]: (r1_tarski(A_3, A_114) | ~r1_tarski(A_3, k3_xboole_0(A_113, A_114)))), inference(resolution, [status(thm)], [c_1133, c_4])).
% 3.20/1.51  tff(c_1467, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1462, c_1181])).
% 3.20/1.51  tff(c_1481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1467])).
% 3.20/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  
% 3.20/1.51  Inference rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Ref     : 0
% 3.20/1.51  #Sup     : 340
% 3.20/1.51  #Fact    : 0
% 3.20/1.51  #Define  : 0
% 3.20/1.51  #Split   : 1
% 3.20/1.51  #Chain   : 0
% 3.20/1.51  #Close   : 0
% 3.20/1.51  
% 3.20/1.51  Ordering : KBO
% 3.20/1.51  
% 3.20/1.51  Simplification rules
% 3.20/1.51  ----------------------
% 3.20/1.51  #Subsume      : 18
% 3.20/1.51  #Demod        : 236
% 3.20/1.51  #Tautology    : 184
% 3.20/1.51  #SimpNegUnit  : 1
% 3.20/1.51  #BackRed      : 6
% 3.20/1.51  
% 3.20/1.51  #Partial instantiations: 0
% 3.20/1.51  #Strategies tried      : 1
% 3.20/1.51  
% 3.20/1.51  Timing (in seconds)
% 3.20/1.51  ----------------------
% 3.20/1.52  Preprocessing        : 0.32
% 3.20/1.52  Parsing              : 0.18
% 3.20/1.52  CNF conversion       : 0.02
% 3.20/1.52  Main loop            : 0.43
% 3.20/1.52  Inferencing          : 0.16
% 3.20/1.52  Reduction            : 0.14
% 3.20/1.52  Demodulation         : 0.10
% 3.20/1.52  BG Simplification    : 0.02
% 3.20/1.52  Subsumption          : 0.08
% 3.20/1.52  Abstraction          : 0.02
% 3.20/1.52  MUC search           : 0.00
% 3.20/1.52  Cooper               : 0.00
% 3.20/1.52  Total                : 0.79
% 3.20/1.52  Index Insertion      : 0.00
% 3.20/1.52  Index Deletion       : 0.00
% 3.20/1.52  Index Matching       : 0.00
% 3.20/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
