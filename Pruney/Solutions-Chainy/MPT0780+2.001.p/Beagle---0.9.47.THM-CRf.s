%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:39 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   77 (  93 expanded)
%              Number of leaves         :   41 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 122 expanded)
%              Number of equality atoms :   37 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_100,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_116,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_85,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_131,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_52,plain,(
    ! [A_59] : v1_relat_1(k6_relat_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    ! [A_54] : k2_relat_1(k6_relat_1(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    ! [B_61,A_60] : k5_relat_1(k6_relat_1(B_61),k6_relat_1(A_60)) = k6_relat_1(k3_xboole_0(A_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1538,plain,(
    ! [B_183,A_184] :
      ( k9_relat_1(B_183,k2_relat_1(A_184)) = k2_relat_1(k5_relat_1(A_184,B_183))
      | ~ v1_relat_1(B_183)
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1566,plain,(
    ! [A_54,B_183] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_54),B_183)) = k9_relat_1(B_183,A_54)
      | ~ v1_relat_1(B_183)
      | ~ v1_relat_1(k6_relat_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1538])).

tff(c_1588,plain,(
    ! [A_190,B_191] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_190),B_191)) = k9_relat_1(B_191,A_190)
      | ~ v1_relat_1(B_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1566])).

tff(c_1618,plain,(
    ! [A_60,B_61] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_60,B_61))) = k9_relat_1(k6_relat_1(A_60),B_61)
      | ~ v1_relat_1(k6_relat_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1588])).

tff(c_1625,plain,(
    ! [A_192,B_193] : k9_relat_1(k6_relat_1(A_192),B_193) = k3_xboole_0(A_192,B_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_1618])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_54] : k1_relat_1(k6_relat_1(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1045,plain,(
    ! [A_160,B_161] :
      ( r1_tarski(k1_relat_1(A_160),k1_relat_1(B_161))
      | ~ r1_tarski(A_160,B_161)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1063,plain,(
    ! [A_160,A_54] :
      ( r1_tarski(k1_relat_1(A_160),A_54)
      | ~ r1_tarski(A_160,k6_relat_1(A_54))
      | ~ v1_relat_1(k6_relat_1(A_54))
      | ~ v1_relat_1(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1045])).

tff(c_1087,plain,(
    ! [A_164,A_165] :
      ( r1_tarski(k1_relat_1(A_164),A_165)
      | ~ r1_tarski(A_164,k6_relat_1(A_165))
      | ~ v1_relat_1(A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1063])).

tff(c_64,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_244,plain,(
    ! [A_96,C_97,B_98] :
      ( r1_tarski(A_96,C_97)
      | ~ r1_tarski(B_98,C_97)
      | ~ r1_tarski(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_253,plain,(
    ! [A_96] :
      ( r1_tarski(A_96,'#skF_2')
      | ~ r1_tarski(A_96,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_64,c_244])).

tff(c_351,plain,(
    ! [B_113,A_114] :
      ( k7_relat_1(B_113,A_114) = B_113
      | ~ r1_tarski(k1_relat_1(B_113),A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_363,plain,(
    ! [B_113] :
      ( k7_relat_1(B_113,'#skF_2') = B_113
      | ~ v1_relat_1(B_113)
      | ~ r1_tarski(k1_relat_1(B_113),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_253,c_351])).

tff(c_1140,plain,(
    ! [A_166] :
      ( k7_relat_1(A_166,'#skF_2') = A_166
      | ~ r1_tarski(A_166,k6_relat_1('#skF_1'))
      | ~ v1_relat_1(A_166) ) ),
    inference(resolution,[status(thm)],[c_1087,c_363])).

tff(c_1156,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k6_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1140])).

tff(c_1164,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1156])).

tff(c_36,plain,(
    ! [B_47,A_46] :
      ( k2_relat_1(k7_relat_1(B_47,A_46)) = k9_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1186,plain,
    ( k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k2_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_36])).

tff(c_1216,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_1186])).

tff(c_1635,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1625,c_1216])).

tff(c_66,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    ! [A_76,B_77] : k1_setfam_1(k2_tarski(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_168,plain,(
    ! [B_88,A_89] : k1_setfam_1(k2_tarski(B_88,A_89)) = k3_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_123])).

tff(c_24,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_174,plain,(
    ! [B_88,A_89] : k3_xboole_0(B_88,A_89) = k3_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_24])).

tff(c_1357,plain,(
    ! [C_172,A_173,B_174] :
      ( k2_wellord1(k2_wellord1(C_172,A_173),B_174) = k2_wellord1(C_172,k3_xboole_0(A_173,B_174))
      | ~ v1_relat_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_62,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1366,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_62])).

tff(c_1381,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_174,c_1366])).

tff(c_1724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1635,c_1381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:48:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.65  
% 3.72/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.65  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.72/1.65  
% 3.72/1.65  %Foreground sorts:
% 3.72/1.65  
% 3.72/1.65  
% 3.72/1.65  %Background operators:
% 3.72/1.65  
% 3.72/1.65  
% 3.72/1.65  %Foreground operators:
% 3.72/1.65  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.72/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.72/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.72/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.72/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.72/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.72/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.72/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.72/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.72/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.72/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.72/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.72/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.72/1.65  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.72/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.72/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.72/1.65  
% 3.72/1.66  tff(f_114, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.72/1.66  tff(f_100, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.72/1.66  tff(f_116, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.72/1.66  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.72/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.72/1.66  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.72/1.66  tff(f_131, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 3.72/1.66  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.72/1.66  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.72/1.66  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.72/1.66  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.72/1.66  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.72/1.66  tff(f_124, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 3.72/1.66  tff(c_52, plain, (![A_59]: (v1_relat_1(k6_relat_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.72/1.66  tff(c_46, plain, (![A_54]: (k2_relat_1(k6_relat_1(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.72/1.66  tff(c_56, plain, (![B_61, A_60]: (k5_relat_1(k6_relat_1(B_61), k6_relat_1(A_60))=k6_relat_1(k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.72/1.66  tff(c_1538, plain, (![B_183, A_184]: (k9_relat_1(B_183, k2_relat_1(A_184))=k2_relat_1(k5_relat_1(A_184, B_183)) | ~v1_relat_1(B_183) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.72/1.66  tff(c_1566, plain, (![A_54, B_183]: (k2_relat_1(k5_relat_1(k6_relat_1(A_54), B_183))=k9_relat_1(B_183, A_54) | ~v1_relat_1(B_183) | ~v1_relat_1(k6_relat_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1538])).
% 3.72/1.66  tff(c_1588, plain, (![A_190, B_191]: (k2_relat_1(k5_relat_1(k6_relat_1(A_190), B_191))=k9_relat_1(B_191, A_190) | ~v1_relat_1(B_191))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1566])).
% 3.72/1.66  tff(c_1618, plain, (![A_60, B_61]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_60, B_61)))=k9_relat_1(k6_relat_1(A_60), B_61) | ~v1_relat_1(k6_relat_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1588])).
% 3.72/1.66  tff(c_1625, plain, (![A_192, B_193]: (k9_relat_1(k6_relat_1(A_192), B_193)=k3_xboole_0(A_192, B_193))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_1618])).
% 3.72/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.72/1.66  tff(c_44, plain, (![A_54]: (k1_relat_1(k6_relat_1(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.72/1.66  tff(c_1045, plain, (![A_160, B_161]: (r1_tarski(k1_relat_1(A_160), k1_relat_1(B_161)) | ~r1_tarski(A_160, B_161) | ~v1_relat_1(B_161) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.72/1.66  tff(c_1063, plain, (![A_160, A_54]: (r1_tarski(k1_relat_1(A_160), A_54) | ~r1_tarski(A_160, k6_relat_1(A_54)) | ~v1_relat_1(k6_relat_1(A_54)) | ~v1_relat_1(A_160))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1045])).
% 3.72/1.66  tff(c_1087, plain, (![A_164, A_165]: (r1_tarski(k1_relat_1(A_164), A_165) | ~r1_tarski(A_164, k6_relat_1(A_165)) | ~v1_relat_1(A_164))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1063])).
% 3.72/1.66  tff(c_64, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.72/1.66  tff(c_244, plain, (![A_96, C_97, B_98]: (r1_tarski(A_96, C_97) | ~r1_tarski(B_98, C_97) | ~r1_tarski(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.72/1.66  tff(c_253, plain, (![A_96]: (r1_tarski(A_96, '#skF_2') | ~r1_tarski(A_96, '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_244])).
% 3.72/1.66  tff(c_351, plain, (![B_113, A_114]: (k7_relat_1(B_113, A_114)=B_113 | ~r1_tarski(k1_relat_1(B_113), A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.72/1.66  tff(c_363, plain, (![B_113]: (k7_relat_1(B_113, '#skF_2')=B_113 | ~v1_relat_1(B_113) | ~r1_tarski(k1_relat_1(B_113), '#skF_1'))), inference(resolution, [status(thm)], [c_253, c_351])).
% 3.72/1.66  tff(c_1140, plain, (![A_166]: (k7_relat_1(A_166, '#skF_2')=A_166 | ~r1_tarski(A_166, k6_relat_1('#skF_1')) | ~v1_relat_1(A_166))), inference(resolution, [status(thm)], [c_1087, c_363])).
% 3.72/1.66  tff(c_1156, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k6_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1140])).
% 3.72/1.66  tff(c_1164, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1156])).
% 3.72/1.66  tff(c_36, plain, (![B_47, A_46]: (k2_relat_1(k7_relat_1(B_47, A_46))=k9_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.72/1.66  tff(c_1186, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k2_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1164, c_36])).
% 3.72/1.66  tff(c_1216, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_1186])).
% 3.72/1.66  tff(c_1635, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1625, c_1216])).
% 3.72/1.66  tff(c_66, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.72/1.66  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.72/1.66  tff(c_123, plain, (![A_76, B_77]: (k1_setfam_1(k2_tarski(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.72/1.66  tff(c_168, plain, (![B_88, A_89]: (k1_setfam_1(k2_tarski(B_88, A_89))=k3_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_10, c_123])).
% 3.72/1.66  tff(c_24, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.72/1.66  tff(c_174, plain, (![B_88, A_89]: (k3_xboole_0(B_88, A_89)=k3_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_168, c_24])).
% 3.72/1.66  tff(c_1357, plain, (![C_172, A_173, B_174]: (k2_wellord1(k2_wellord1(C_172, A_173), B_174)=k2_wellord1(C_172, k3_xboole_0(A_173, B_174)) | ~v1_relat_1(C_172))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.72/1.66  tff(c_62, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.72/1.66  tff(c_1366, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1357, c_62])).
% 3.72/1.66  tff(c_1381, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_174, c_1366])).
% 3.72/1.66  tff(c_1724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1635, c_1381])).
% 3.72/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.66  
% 3.72/1.66  Inference rules
% 3.72/1.66  ----------------------
% 3.72/1.66  #Ref     : 0
% 3.72/1.66  #Sup     : 354
% 3.72/1.66  #Fact    : 0
% 3.72/1.66  #Define  : 0
% 3.72/1.66  #Split   : 2
% 3.72/1.66  #Chain   : 0
% 3.72/1.66  #Close   : 0
% 3.72/1.66  
% 3.72/1.66  Ordering : KBO
% 3.72/1.66  
% 3.72/1.66  Simplification rules
% 3.72/1.66  ----------------------
% 3.72/1.66  #Subsume      : 32
% 3.72/1.66  #Demod        : 226
% 3.72/1.66  #Tautology    : 188
% 3.72/1.66  #SimpNegUnit  : 0
% 3.72/1.66  #BackRed      : 3
% 3.72/1.66  
% 3.72/1.66  #Partial instantiations: 0
% 3.72/1.66  #Strategies tried      : 1
% 3.72/1.66  
% 3.72/1.66  Timing (in seconds)
% 3.72/1.66  ----------------------
% 3.72/1.67  Preprocessing        : 0.36
% 3.72/1.67  Parsing              : 0.20
% 3.72/1.67  CNF conversion       : 0.02
% 3.72/1.67  Main loop            : 0.47
% 3.72/1.67  Inferencing          : 0.17
% 3.72/1.67  Reduction            : 0.16
% 3.72/1.67  Demodulation         : 0.12
% 3.72/1.67  BG Simplification    : 0.03
% 3.72/1.67  Subsumption          : 0.09
% 3.72/1.67  Abstraction          : 0.03
% 3.72/1.67  MUC search           : 0.00
% 3.72/1.67  Cooper               : 0.00
% 3.72/1.67  Total                : 0.87
% 3.72/1.67  Index Insertion      : 0.00
% 3.72/1.67  Index Deletion       : 0.00
% 3.72/1.67  Index Matching       : 0.00
% 3.72/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
