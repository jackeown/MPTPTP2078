%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:42 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 196 expanded)
%              Number of leaves         :   39 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  114 ( 331 expanded)
%              Number of equality atoms :   49 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_90,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_38,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ! [A_39] : k2_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_372,plain,(
    ! [A_96,B_97] :
      ( k8_relat_1(A_96,B_97) = B_97
      | ~ r1_tarski(k2_relat_1(B_97),A_96)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_395,plain,(
    ! [B_98] :
      ( k8_relat_1(k2_relat_1(B_98),B_98) = B_98
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_6,c_372])).

tff(c_416,plain,(
    ! [A_39] :
      ( k8_relat_1(A_39,k6_relat_1(A_39)) = k6_relat_1(A_39)
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_395])).

tff(c_421,plain,(
    ! [A_39] : k8_relat_1(A_39,k6_relat_1(A_39)) = k6_relat_1(A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_416])).

tff(c_24,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_30,B_31)),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_111,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,'#skF_2')
      | ~ r1_tarski(A_68,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_111])).

tff(c_541,plain,(
    ! [B_108] :
      ( k8_relat_1('#skF_2',B_108) = B_108
      | ~ v1_relat_1(B_108)
      | ~ r1_tarski(k2_relat_1(B_108),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_120,c_372])).

tff(c_871,plain,(
    ! [B_123] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_123)) = k8_relat_1('#skF_1',B_123)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_123))
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_24,c_541])).

tff(c_879,plain,
    ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',k6_relat_1('#skF_1'))) = k8_relat_1('#skF_1',k6_relat_1('#skF_1'))
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_871])).

tff(c_887,plain,(
    k8_relat_1('#skF_2',k6_relat_1('#skF_1')) = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_421,c_421,c_879])).

tff(c_44,plain,(
    ! [A_45,B_46] :
      ( k7_relat_1(k8_relat_1(A_45,B_46),A_45) = k2_wellord1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_904,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k2_wellord1(k6_relat_1('#skF_1'),'#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_44])).

tff(c_930,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k2_wellord1(k6_relat_1('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_904])).

tff(c_32,plain,(
    ! [A_39] : k1_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    ! [B_82,A_83] :
      ( k7_relat_1(B_82,A_83) = B_82
      | ~ r1_tarski(k1_relat_1(B_82),A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_309,plain,(
    ! [B_93] :
      ( k7_relat_1(B_93,'#skF_2') = B_93
      | ~ v1_relat_1(B_93)
      | ~ r1_tarski(k1_relat_1(B_93),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_120,c_178])).

tff(c_312,plain,(
    ! [A_39] :
      ( k7_relat_1(k6_relat_1(A_39),'#skF_2') = k6_relat_1(A_39)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ r1_tarski(A_39,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_309])).

tff(c_314,plain,(
    ! [A_39] :
      ( k7_relat_1(k6_relat_1(A_39),'#skF_2') = k6_relat_1(A_39)
      | ~ r1_tarski(A_39,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_312])).

tff(c_951,plain,
    ( k2_wellord1(k6_relat_1('#skF_1'),'#skF_2') = k6_relat_1('#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_930,c_314])).

tff(c_979,plain,(
    k2_wellord1(k6_relat_1('#skF_1'),'#skF_2') = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_951])).

tff(c_995,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_930])).

tff(c_28,plain,(
    ! [B_35,A_34] :
      ( k2_relat_1(k7_relat_1(B_35,A_34)) = k9_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1105,plain,
    ( k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k2_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_28])).

tff(c_1131,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_1105])).

tff(c_42,plain,(
    ! [B_44,A_43] : k5_relat_1(k6_relat_1(B_44),k6_relat_1(A_43)) = k6_relat_1(k3_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1237,plain,(
    ! [B_130,A_131] :
      ( k9_relat_1(B_130,k2_relat_1(A_131)) = k2_relat_1(k5_relat_1(A_131,B_130))
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1265,plain,(
    ! [A_39,B_130] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_39),B_130)) = k9_relat_1(B_130,A_39)
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1237])).

tff(c_1278,plain,(
    ! [A_132,B_133] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_132),B_133)) = k9_relat_1(B_133,A_132)
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1265])).

tff(c_1299,plain,(
    ! [A_43,B_44] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_43,B_44))) = k9_relat_1(k6_relat_1(A_43),B_44)
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1278])).

tff(c_1306,plain,(
    ! [A_134,B_135] : k9_relat_1(k6_relat_1(A_134),B_135) = k3_xboole_0(A_134,B_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_1299])).

tff(c_1334,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1131,c_1306])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1016,plain,(
    ! [C_124,A_125,B_126] :
      ( k2_wellord1(k2_wellord1(C_124,A_125),B_126) = k2_wellord1(C_124,k3_xboole_0(A_125,B_126))
      | ~ v1_relat_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_753,plain,(
    ! [C_118,B_119,A_120] :
      ( k2_wellord1(k2_wellord1(C_118,B_119),A_120) = k2_wellord1(k2_wellord1(C_118,A_120),B_119)
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_50,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_780,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_50])).

tff(c_819,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_780])).

tff(c_1029,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_819])).

tff(c_1079,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1029])).

tff(c_1392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_1079])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.49  
% 3.18/1.49  %Foreground sorts:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Background operators:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Foreground operators:
% 3.18/1.49  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.18/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.18/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.18/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.18/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.18/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.18/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.18/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.18/1.49  
% 3.18/1.51  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.18/1.51  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.18/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.18/1.51  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 3.18/1.51  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 3.18/1.51  tff(f_109, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 3.18/1.51  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.18/1.51  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 3.18/1.51  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.18/1.51  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.18/1.51  tff(f_90, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.18/1.51  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.18/1.51  tff(f_98, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 3.18/1.51  tff(f_102, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 3.18/1.51  tff(c_38, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.18/1.51  tff(c_34, plain, (![A_39]: (k2_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.51  tff(c_372, plain, (![A_96, B_97]: (k8_relat_1(A_96, B_97)=B_97 | ~r1_tarski(k2_relat_1(B_97), A_96) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.18/1.51  tff(c_395, plain, (![B_98]: (k8_relat_1(k2_relat_1(B_98), B_98)=B_98 | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_6, c_372])).
% 3.18/1.51  tff(c_416, plain, (![A_39]: (k8_relat_1(A_39, k6_relat_1(A_39))=k6_relat_1(A_39) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_395])).
% 3.18/1.51  tff(c_421, plain, (![A_39]: (k8_relat_1(A_39, k6_relat_1(A_39))=k6_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_416])).
% 3.18/1.51  tff(c_24, plain, (![A_30, B_31]: (r1_tarski(k2_relat_1(k8_relat_1(A_30, B_31)), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.51  tff(c_52, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.51  tff(c_111, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.51  tff(c_120, plain, (![A_68]: (r1_tarski(A_68, '#skF_2') | ~r1_tarski(A_68, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_111])).
% 3.18/1.51  tff(c_541, plain, (![B_108]: (k8_relat_1('#skF_2', B_108)=B_108 | ~v1_relat_1(B_108) | ~r1_tarski(k2_relat_1(B_108), '#skF_1'))), inference(resolution, [status(thm)], [c_120, c_372])).
% 3.18/1.51  tff(c_871, plain, (![B_123]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_123))=k8_relat_1('#skF_1', B_123) | ~v1_relat_1(k8_relat_1('#skF_1', B_123)) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_24, c_541])).
% 3.18/1.51  tff(c_879, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', k6_relat_1('#skF_1')))=k8_relat_1('#skF_1', k6_relat_1('#skF_1')) | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_421, c_871])).
% 3.18/1.51  tff(c_887, plain, (k8_relat_1('#skF_2', k6_relat_1('#skF_1'))=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_421, c_421, c_879])).
% 3.18/1.51  tff(c_44, plain, (![A_45, B_46]: (k7_relat_1(k8_relat_1(A_45, B_46), A_45)=k2_wellord1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.18/1.51  tff(c_904, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k2_wellord1(k6_relat_1('#skF_1'), '#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_887, c_44])).
% 3.18/1.51  tff(c_930, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k2_wellord1(k6_relat_1('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_904])).
% 3.18/1.51  tff(c_32, plain, (![A_39]: (k1_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.51  tff(c_178, plain, (![B_82, A_83]: (k7_relat_1(B_82, A_83)=B_82 | ~r1_tarski(k1_relat_1(B_82), A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.18/1.51  tff(c_309, plain, (![B_93]: (k7_relat_1(B_93, '#skF_2')=B_93 | ~v1_relat_1(B_93) | ~r1_tarski(k1_relat_1(B_93), '#skF_1'))), inference(resolution, [status(thm)], [c_120, c_178])).
% 3.18/1.51  tff(c_312, plain, (![A_39]: (k7_relat_1(k6_relat_1(A_39), '#skF_2')=k6_relat_1(A_39) | ~v1_relat_1(k6_relat_1(A_39)) | ~r1_tarski(A_39, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_309])).
% 3.18/1.51  tff(c_314, plain, (![A_39]: (k7_relat_1(k6_relat_1(A_39), '#skF_2')=k6_relat_1(A_39) | ~r1_tarski(A_39, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_312])).
% 3.18/1.51  tff(c_951, plain, (k2_wellord1(k6_relat_1('#skF_1'), '#skF_2')=k6_relat_1('#skF_1') | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_930, c_314])).
% 3.18/1.51  tff(c_979, plain, (k2_wellord1(k6_relat_1('#skF_1'), '#skF_2')=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_951])).
% 3.18/1.51  tff(c_995, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_979, c_930])).
% 3.18/1.51  tff(c_28, plain, (![B_35, A_34]: (k2_relat_1(k7_relat_1(B_35, A_34))=k9_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.18/1.51  tff(c_1105, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k2_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_995, c_28])).
% 3.18/1.51  tff(c_1131, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_1105])).
% 3.18/1.51  tff(c_42, plain, (![B_44, A_43]: (k5_relat_1(k6_relat_1(B_44), k6_relat_1(A_43))=k6_relat_1(k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.18/1.51  tff(c_1237, plain, (![B_130, A_131]: (k9_relat_1(B_130, k2_relat_1(A_131))=k2_relat_1(k5_relat_1(A_131, B_130)) | ~v1_relat_1(B_130) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.18/1.51  tff(c_1265, plain, (![A_39, B_130]: (k2_relat_1(k5_relat_1(k6_relat_1(A_39), B_130))=k9_relat_1(B_130, A_39) | ~v1_relat_1(B_130) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1237])).
% 3.18/1.51  tff(c_1278, plain, (![A_132, B_133]: (k2_relat_1(k5_relat_1(k6_relat_1(A_132), B_133))=k9_relat_1(B_133, A_132) | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1265])).
% 3.18/1.51  tff(c_1299, plain, (![A_43, B_44]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_43, B_44)))=k9_relat_1(k6_relat_1(A_43), B_44) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1278])).
% 3.18/1.51  tff(c_1306, plain, (![A_134, B_135]: (k9_relat_1(k6_relat_1(A_134), B_135)=k3_xboole_0(A_134, B_135))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_1299])).
% 3.18/1.51  tff(c_1334, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1131, c_1306])).
% 3.18/1.51  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.51  tff(c_1016, plain, (![C_124, A_125, B_126]: (k2_wellord1(k2_wellord1(C_124, A_125), B_126)=k2_wellord1(C_124, k3_xboole_0(A_125, B_126)) | ~v1_relat_1(C_124))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.18/1.51  tff(c_753, plain, (![C_118, B_119, A_120]: (k2_wellord1(k2_wellord1(C_118, B_119), A_120)=k2_wellord1(k2_wellord1(C_118, A_120), B_119) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.18/1.51  tff(c_50, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.18/1.51  tff(c_780, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_753, c_50])).
% 3.18/1.51  tff(c_819, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_780])).
% 3.18/1.51  tff(c_1029, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1016, c_819])).
% 3.18/1.51  tff(c_1079, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1029])).
% 3.18/1.51  tff(c_1392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1334, c_1079])).
% 3.18/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  Inference rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Ref     : 0
% 3.18/1.51  #Sup     : 294
% 3.18/1.51  #Fact    : 0
% 3.18/1.51  #Define  : 0
% 3.18/1.51  #Split   : 1
% 3.18/1.51  #Chain   : 0
% 3.18/1.51  #Close   : 0
% 3.18/1.51  
% 3.18/1.51  Ordering : KBO
% 3.18/1.51  
% 3.18/1.51  Simplification rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Subsume      : 29
% 3.18/1.51  #Demod        : 222
% 3.18/1.51  #Tautology    : 159
% 3.18/1.51  #SimpNegUnit  : 0
% 3.18/1.51  #BackRed      : 4
% 3.18/1.51  
% 3.18/1.51  #Partial instantiations: 0
% 3.18/1.51  #Strategies tried      : 1
% 3.18/1.51  
% 3.18/1.51  Timing (in seconds)
% 3.18/1.51  ----------------------
% 3.18/1.51  Preprocessing        : 0.34
% 3.18/1.51  Parsing              : 0.18
% 3.18/1.51  CNF conversion       : 0.02
% 3.18/1.51  Main loop            : 0.40
% 3.18/1.51  Inferencing          : 0.15
% 3.18/1.51  Reduction            : 0.12
% 3.18/1.51  Demodulation         : 0.09
% 3.18/1.51  BG Simplification    : 0.03
% 3.18/1.51  Subsumption          : 0.08
% 3.18/1.51  Abstraction          : 0.03
% 3.18/1.51  MUC search           : 0.00
% 3.18/1.51  Cooper               : 0.00
% 3.18/1.51  Total                : 0.78
% 3.18/1.51  Index Insertion      : 0.00
% 3.18/1.51  Index Deletion       : 0.00
% 3.18/1.51  Index Matching       : 0.00
% 3.18/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
