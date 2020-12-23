%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:41 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 113 expanded)
%              Number of leaves         :   36 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 161 expanded)
%              Number of equality atoms :   36 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_88,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_22,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [A_38] : k2_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [B_44,A_43] : k5_relat_1(k6_relat_1(B_44),k6_relat_1(A_43)) = k6_relat_1(k3_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1063,plain,(
    ! [B_134,A_135] :
      ( k9_relat_1(B_134,k2_relat_1(A_135)) = k2_relat_1(k5_relat_1(A_135,B_134))
      | ~ v1_relat_1(B_134)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1091,plain,(
    ! [A_38,B_134] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_38),B_134)) = k9_relat_1(B_134,A_38)
      | ~ v1_relat_1(B_134)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1063])).

tff(c_1104,plain,(
    ! [A_136,B_137] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_136),B_137)) = k9_relat_1(B_137,A_136)
      | ~ v1_relat_1(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1091])).

tff(c_1125,plain,(
    ! [A_43,B_44] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_43,B_44))) = k9_relat_1(k6_relat_1(A_43),B_44)
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1104])).

tff(c_1129,plain,(
    ! [A_43,B_44] : k9_relat_1(k6_relat_1(A_43),B_44) = k3_xboole_0(A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_34,c_1125])).

tff(c_32,plain,(
    ! [A_38] : k1_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [B_85,A_86] :
      ( k7_relat_1(B_85,A_86) = B_85
      | ~ r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_198,plain,(
    ! [B_87] :
      ( k7_relat_1(B_87,k1_relat_1(B_87)) = B_87
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_213,plain,(
    ! [A_38] :
      ( k7_relat_1(k6_relat_1(A_38),A_38) = k6_relat_1(A_38)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_198])).

tff(c_218,plain,(
    ! [A_38] : k7_relat_1(k6_relat_1(A_38),A_38) = k6_relat_1(A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_213])).

tff(c_36,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_40,A_39)),A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_138,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_tarski(A_78,C_79)
      | ~ r1_tarski(B_80,C_79)
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,'#skF_2')
      | ~ r1_tarski(A_78,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_138])).

tff(c_330,plain,(
    ! [B_96] :
      ( k7_relat_1(B_96,'#skF_2') = B_96
      | ~ v1_relat_1(B_96)
      | ~ r1_tarski(k1_relat_1(B_96),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_147,c_178])).

tff(c_1172,plain,(
    ! [B_140] :
      ( k7_relat_1(k7_relat_1(B_140,'#skF_1'),'#skF_2') = k7_relat_1(B_140,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_140,'#skF_1'))
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_36,c_330])).

tff(c_1188,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'),'#skF_1'),'#skF_2') = k7_relat_1(k6_relat_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_1172])).

tff(c_1194,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_218,c_218,c_1188])).

tff(c_28,plain,(
    ! [B_34,A_33] :
      ( k2_relat_1(k7_relat_1(B_34,A_33)) = k9_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1228,plain,
    ( k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k2_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_28])).

tff(c_1261,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1129,c_34,c_1228])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_992,plain,(
    ! [C_131,A_132,B_133] :
      ( k2_wellord1(k2_wellord1(C_131,A_132),B_133) = k2_wellord1(C_131,k3_xboole_0(A_132,B_133))
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_765,plain,(
    ! [C_122,B_123,A_124] :
      ( k2_wellord1(k2_wellord1(C_122,B_123),A_124) = k2_wellord1(k2_wellord1(C_122,A_124),B_123)
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_792,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_50])).

tff(c_837,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_792])).

tff(c_1005,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_837])).

tff(c_1055,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1005])).

tff(c_1286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_1055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.53  
% 3.16/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.53  %$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.16/1.53  
% 3.16/1.53  %Foreground sorts:
% 3.16/1.53  
% 3.16/1.53  
% 3.16/1.53  %Background operators:
% 3.16/1.53  
% 3.16/1.53  
% 3.16/1.53  %Foreground operators:
% 3.16/1.53  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.16/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.16/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.16/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.53  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.16/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.16/1.53  
% 3.32/1.54  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.32/1.54  tff(f_76, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.32/1.54  tff(f_88, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.32/1.54  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.32/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.54  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.32/1.54  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.32/1.54  tff(f_111, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 3.32/1.54  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.32/1.54  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.32/1.54  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 3.32/1.54  tff(f_104, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_wellord1)).
% 3.32/1.54  tff(c_22, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.32/1.54  tff(c_34, plain, (![A_38]: (k2_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.54  tff(c_40, plain, (![B_44, A_43]: (k5_relat_1(k6_relat_1(B_44), k6_relat_1(A_43))=k6_relat_1(k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.32/1.54  tff(c_1063, plain, (![B_134, A_135]: (k9_relat_1(B_134, k2_relat_1(A_135))=k2_relat_1(k5_relat_1(A_135, B_134)) | ~v1_relat_1(B_134) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.54  tff(c_1091, plain, (![A_38, B_134]: (k2_relat_1(k5_relat_1(k6_relat_1(A_38), B_134))=k9_relat_1(B_134, A_38) | ~v1_relat_1(B_134) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1063])).
% 3.32/1.54  tff(c_1104, plain, (![A_136, B_137]: (k2_relat_1(k5_relat_1(k6_relat_1(A_136), B_137))=k9_relat_1(B_137, A_136) | ~v1_relat_1(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1091])).
% 3.32/1.54  tff(c_1125, plain, (![A_43, B_44]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_43, B_44)))=k9_relat_1(k6_relat_1(A_43), B_44) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1104])).
% 3.32/1.54  tff(c_1129, plain, (![A_43, B_44]: (k9_relat_1(k6_relat_1(A_43), B_44)=k3_xboole_0(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_34, c_1125])).
% 3.32/1.54  tff(c_32, plain, (![A_38]: (k1_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.32/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.54  tff(c_178, plain, (![B_85, A_86]: (k7_relat_1(B_85, A_86)=B_85 | ~r1_tarski(k1_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.32/1.54  tff(c_198, plain, (![B_87]: (k7_relat_1(B_87, k1_relat_1(B_87))=B_87 | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_6, c_178])).
% 3.32/1.54  tff(c_213, plain, (![A_38]: (k7_relat_1(k6_relat_1(A_38), A_38)=k6_relat_1(A_38) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_198])).
% 3.32/1.54  tff(c_218, plain, (![A_38]: (k7_relat_1(k6_relat_1(A_38), A_38)=k6_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_213])).
% 3.32/1.54  tff(c_36, plain, (![B_40, A_39]: (r1_tarski(k1_relat_1(k7_relat_1(B_40, A_39)), A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.32/1.54  tff(c_52, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.32/1.54  tff(c_138, plain, (![A_78, C_79, B_80]: (r1_tarski(A_78, C_79) | ~r1_tarski(B_80, C_79) | ~r1_tarski(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.54  tff(c_147, plain, (![A_78]: (r1_tarski(A_78, '#skF_2') | ~r1_tarski(A_78, '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_138])).
% 3.32/1.54  tff(c_330, plain, (![B_96]: (k7_relat_1(B_96, '#skF_2')=B_96 | ~v1_relat_1(B_96) | ~r1_tarski(k1_relat_1(B_96), '#skF_1'))), inference(resolution, [status(thm)], [c_147, c_178])).
% 3.32/1.54  tff(c_1172, plain, (![B_140]: (k7_relat_1(k7_relat_1(B_140, '#skF_1'), '#skF_2')=k7_relat_1(B_140, '#skF_1') | ~v1_relat_1(k7_relat_1(B_140, '#skF_1')) | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_36, c_330])).
% 3.32/1.54  tff(c_1188, plain, (k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'), '#skF_1'), '#skF_2')=k7_relat_1(k6_relat_1('#skF_1'), '#skF_1') | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_1172])).
% 3.32/1.54  tff(c_1194, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_218, c_218, c_1188])).
% 3.32/1.54  tff(c_28, plain, (![B_34, A_33]: (k2_relat_1(k7_relat_1(B_34, A_33))=k9_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.32/1.54  tff(c_1228, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k2_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1194, c_28])).
% 3.32/1.54  tff(c_1261, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1129, c_34, c_1228])).
% 3.32/1.54  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.32/1.54  tff(c_992, plain, (![C_131, A_132, B_133]: (k2_wellord1(k2_wellord1(C_131, A_132), B_133)=k2_wellord1(C_131, k3_xboole_0(A_132, B_133)) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.54  tff(c_765, plain, (![C_122, B_123, A_124]: (k2_wellord1(k2_wellord1(C_122, B_123), A_124)=k2_wellord1(k2_wellord1(C_122, A_124), B_123) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.32/1.54  tff(c_50, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.32/1.54  tff(c_792, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_765, c_50])).
% 3.32/1.54  tff(c_837, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_792])).
% 3.32/1.54  tff(c_1005, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_992, c_837])).
% 3.32/1.54  tff(c_1055, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1005])).
% 3.32/1.54  tff(c_1286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1261, c_1055])).
% 3.32/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.54  
% 3.32/1.54  Inference rules
% 3.32/1.54  ----------------------
% 3.32/1.54  #Ref     : 0
% 3.32/1.54  #Sup     : 274
% 3.32/1.54  #Fact    : 0
% 3.32/1.54  #Define  : 0
% 3.32/1.54  #Split   : 1
% 3.32/1.54  #Chain   : 0
% 3.32/1.54  #Close   : 0
% 3.32/1.54  
% 3.32/1.54  Ordering : KBO
% 3.32/1.55  
% 3.32/1.55  Simplification rules
% 3.32/1.55  ----------------------
% 3.32/1.55  #Subsume      : 31
% 3.32/1.55  #Demod        : 179
% 3.32/1.55  #Tautology    : 126
% 3.32/1.55  #SimpNegUnit  : 0
% 3.32/1.55  #BackRed      : 3
% 3.32/1.55  
% 3.32/1.55  #Partial instantiations: 0
% 3.32/1.55  #Strategies tried      : 1
% 3.32/1.55  
% 3.32/1.55  Timing (in seconds)
% 3.32/1.55  ----------------------
% 3.32/1.55  Preprocessing        : 0.37
% 3.32/1.55  Parsing              : 0.19
% 3.32/1.55  CNF conversion       : 0.02
% 3.32/1.55  Main loop            : 0.39
% 3.32/1.55  Inferencing          : 0.15
% 3.32/1.55  Reduction            : 0.12
% 3.32/1.55  Demodulation         : 0.09
% 3.32/1.55  BG Simplification    : 0.03
% 3.32/1.55  Subsumption          : 0.07
% 3.32/1.55  Abstraction          : 0.03
% 3.32/1.55  MUC search           : 0.00
% 3.32/1.55  Cooper               : 0.00
% 3.32/1.55  Total                : 0.79
% 3.32/1.55  Index Insertion      : 0.00
% 3.32/1.55  Index Deletion       : 0.00
% 3.32/1.55  Index Matching       : 0.00
% 3.32/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
