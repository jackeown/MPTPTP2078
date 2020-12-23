%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:49 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   74 (  96 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  119 ( 160 expanded)
%              Number of equality atoms :   39 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_71,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k3_xboole_0(k1_relat_1(B),A),k9_relat_1(k4_relat_1(B),k9_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = k8_relat_1(A_4,B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_240,plain,(
    ! [A_54,B_55] :
      ( k10_relat_1(A_54,k1_relat_1(B_55)) = k1_relat_1(k5_relat_1(A_54,B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_258,plain,(
    ! [A_54,A_17] :
      ( k1_relat_1(k5_relat_1(A_54,k6_relat_1(A_17))) = k10_relat_1(A_54,A_17)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_240])).

tff(c_284,plain,(
    ! [A_58,A_59] :
      ( k1_relat_1(k5_relat_1(A_58,k6_relat_1(A_59))) = k10_relat_1(A_58,A_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_258])).

tff(c_302,plain,(
    ! [A_4,B_5] :
      ( k1_relat_1(k8_relat_1(A_4,B_5)) = k10_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_284])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k8_relat_1(A_2,B_3))
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),B_24) = k7_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [A_18] : k4_relat_1(k6_relat_1(A_18)) = k6_relat_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_265,plain,(
    ! [B_56,A_57] :
      ( k5_relat_1(k4_relat_1(B_56),k4_relat_1(A_57)) = k4_relat_1(k5_relat_1(A_57,B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_274,plain,(
    ! [A_18,A_57] :
      ( k5_relat_1(k6_relat_1(A_18),k4_relat_1(A_57)) = k4_relat_1(k5_relat_1(A_57,k6_relat_1(A_18)))
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_265])).

tff(c_739,plain,(
    ! [A_84,A_85] :
      ( k5_relat_1(k6_relat_1(A_84),k4_relat_1(A_85)) = k4_relat_1(k5_relat_1(A_85,k6_relat_1(A_84)))
      | ~ v1_relat_1(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_274])).

tff(c_957,plain,(
    ! [A_95,A_96] :
      ( k4_relat_1(k5_relat_1(A_95,k6_relat_1(A_96))) = k7_relat_1(k4_relat_1(A_95),A_96)
      | ~ v1_relat_1(A_95)
      | ~ v1_relat_1(k4_relat_1(A_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_739])).

tff(c_1744,plain,(
    ! [B_130,A_131] :
      ( k7_relat_1(k4_relat_1(B_130),A_131) = k4_relat_1(k8_relat_1(A_131,B_130))
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(k4_relat_1(B_130))
      | ~ v1_relat_1(B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_957])).

tff(c_1767,plain,(
    ! [A_132,A_133] :
      ( k7_relat_1(k4_relat_1(A_132),A_133) = k4_relat_1(k8_relat_1(A_133,A_132))
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_2,c_1744])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2001,plain,(
    ! [A_145,A_146] :
      ( k2_relat_1(k4_relat_1(k8_relat_1(A_145,A_146))) = k9_relat_1(k4_relat_1(A_146),A_145)
      | ~ v1_relat_1(k4_relat_1(A_146))
      | ~ v1_relat_1(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_8])).

tff(c_14,plain,(
    ! [A_13] :
      ( k2_relat_1(k4_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3530,plain,(
    ! [A_211,A_212] :
      ( k9_relat_1(k4_relat_1(A_211),A_212) = k1_relat_1(k8_relat_1(A_212,A_211))
      | ~ v1_relat_1(k8_relat_1(A_212,A_211))
      | ~ v1_relat_1(k4_relat_1(A_211))
      | ~ v1_relat_1(A_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2001,c_14])).

tff(c_3549,plain,(
    ! [B_213,A_214] :
      ( k9_relat_1(k4_relat_1(B_213),A_214) = k1_relat_1(k8_relat_1(A_214,B_213))
      | ~ v1_relat_1(k4_relat_1(B_213))
      | ~ v1_relat_1(B_213) ) ),
    inference(resolution,[status(thm)],[c_4,c_3530])).

tff(c_3579,plain,(
    ! [A_215,A_216] :
      ( k9_relat_1(k4_relat_1(A_215),A_216) = k1_relat_1(k8_relat_1(A_216,A_215))
      | ~ v1_relat_1(A_215) ) ),
    inference(resolution,[status(thm)],[c_2,c_3549])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_144,plain,(
    ! [B_42,A_43] :
      ( k3_xboole_0(k1_relat_1(B_42),A_43) = k1_relat_1(k7_relat_1(B_42,A_43))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_156,plain,(
    ! [A_17,A_43] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_17),A_43)) = k3_xboole_0(A_17,A_43)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_144])).

tff(c_160,plain,(
    ! [A_17,A_43] : k1_relat_1(k7_relat_1(k6_relat_1(A_17),A_43)) = k3_xboole_0(A_17,A_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_156])).

tff(c_190,plain,(
    ! [B_50,A_51] :
      ( k1_relat_1(k7_relat_1(B_50,A_51)) = A_51
      | ~ r1_tarski(A_51,k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_199,plain,(
    ! [A_17,A_51] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_17),A_51)) = A_51
      | ~ r1_tarski(A_51,A_17)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_190])).

tff(c_220,plain,(
    ! [A_52,A_53] :
      ( k3_xboole_0(A_52,A_53) = A_53
      | ~ r1_tarski(A_53,A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_160,c_199])).

tff(c_224,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38,c_220])).

tff(c_458,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(B_70),A_71),k9_relat_1(k4_relat_1(B_70),k9_relat_1(B_70,A_71)))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_476,plain,
    ( r1_tarski('#skF_1',k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_458])).

tff(c_497,plain,(
    r1_tarski('#skF_1',k9_relat_1(k4_relat_1('#skF_2'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_476])).

tff(c_3618,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k8_relat_1(k9_relat_1('#skF_2','#skF_1'),'#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3579,c_497])).

tff(c_3653,plain,(
    r1_tarski('#skF_1',k1_relat_1(k8_relat_1(k9_relat_1('#skF_2','#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3618])).

tff(c_3671,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_3653])).

tff(c_3675,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_3671])).

tff(c_3677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.01  
% 5.33/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.01  %$ r1_tarski > v2_funct_1 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.33/2.01  
% 5.33/2.01  %Foreground sorts:
% 5.33/2.01  
% 5.33/2.01  
% 5.33/2.01  %Background operators:
% 5.33/2.01  
% 5.33/2.01  
% 5.33/2.01  %Foreground operators:
% 5.33/2.01  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.33/2.01  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.33/2.01  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.33/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.33/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.01  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.33/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.01  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.33/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.33/2.01  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.33/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.33/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.33/2.01  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.33/2.01  
% 5.33/2.02  tff(f_96, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 5.33/2.02  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 5.33/2.02  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.33/2.02  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.33/2.02  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 5.33/2.02  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.33/2.02  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 5.33/2.02  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 5.33/2.02  tff(f_71, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 5.33/2.02  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 5.33/2.02  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.33/2.02  tff(f_58, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 5.33/2.02  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 5.33/2.02  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 5.33/2.02  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k3_xboole_0(k1_relat_1(B), A), k9_relat_1(k4_relat_1(B), k9_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_relat_1)).
% 5.33/2.02  tff(c_36, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.33/2.02  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.33/2.02  tff(c_6, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=k8_relat_1(A_4, B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.33/2.02  tff(c_32, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.33/2.02  tff(c_20, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.33/2.02  tff(c_240, plain, (![A_54, B_55]: (k10_relat_1(A_54, k1_relat_1(B_55))=k1_relat_1(k5_relat_1(A_54, B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.33/2.02  tff(c_258, plain, (![A_54, A_17]: (k1_relat_1(k5_relat_1(A_54, k6_relat_1(A_17)))=k10_relat_1(A_54, A_17) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_20, c_240])).
% 5.33/2.02  tff(c_284, plain, (![A_58, A_59]: (k1_relat_1(k5_relat_1(A_58, k6_relat_1(A_59)))=k10_relat_1(A_58, A_59) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_258])).
% 5.33/2.02  tff(c_302, plain, (![A_4, B_5]: (k1_relat_1(k8_relat_1(A_4, B_5))=k10_relat_1(B_5, A_4) | ~v1_relat_1(B_5) | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_284])).
% 5.33/2.02  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.33/2.02  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k8_relat_1(A_2, B_3)) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.33/2.02  tff(c_30, plain, (![A_23, B_24]: (k5_relat_1(k6_relat_1(A_23), B_24)=k7_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.33/2.02  tff(c_24, plain, (![A_18]: (k4_relat_1(k6_relat_1(A_18))=k6_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.33/2.02  tff(c_265, plain, (![B_56, A_57]: (k5_relat_1(k4_relat_1(B_56), k4_relat_1(A_57))=k4_relat_1(k5_relat_1(A_57, B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.33/2.02  tff(c_274, plain, (![A_18, A_57]: (k5_relat_1(k6_relat_1(A_18), k4_relat_1(A_57))=k4_relat_1(k5_relat_1(A_57, k6_relat_1(A_18))) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_24, c_265])).
% 5.33/2.02  tff(c_739, plain, (![A_84, A_85]: (k5_relat_1(k6_relat_1(A_84), k4_relat_1(A_85))=k4_relat_1(k5_relat_1(A_85, k6_relat_1(A_84))) | ~v1_relat_1(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_274])).
% 5.33/2.02  tff(c_957, plain, (![A_95, A_96]: (k4_relat_1(k5_relat_1(A_95, k6_relat_1(A_96)))=k7_relat_1(k4_relat_1(A_95), A_96) | ~v1_relat_1(A_95) | ~v1_relat_1(k4_relat_1(A_95)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_739])).
% 5.33/2.02  tff(c_1744, plain, (![B_130, A_131]: (k7_relat_1(k4_relat_1(B_130), A_131)=k4_relat_1(k8_relat_1(A_131, B_130)) | ~v1_relat_1(B_130) | ~v1_relat_1(k4_relat_1(B_130)) | ~v1_relat_1(B_130))), inference(superposition, [status(thm), theory('equality')], [c_6, c_957])).
% 5.33/2.02  tff(c_1767, plain, (![A_132, A_133]: (k7_relat_1(k4_relat_1(A_132), A_133)=k4_relat_1(k8_relat_1(A_133, A_132)) | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_2, c_1744])).
% 5.33/2.02  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.33/2.02  tff(c_2001, plain, (![A_145, A_146]: (k2_relat_1(k4_relat_1(k8_relat_1(A_145, A_146)))=k9_relat_1(k4_relat_1(A_146), A_145) | ~v1_relat_1(k4_relat_1(A_146)) | ~v1_relat_1(A_146))), inference(superposition, [status(thm), theory('equality')], [c_1767, c_8])).
% 5.33/2.02  tff(c_14, plain, (![A_13]: (k2_relat_1(k4_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.33/2.02  tff(c_3530, plain, (![A_211, A_212]: (k9_relat_1(k4_relat_1(A_211), A_212)=k1_relat_1(k8_relat_1(A_212, A_211)) | ~v1_relat_1(k8_relat_1(A_212, A_211)) | ~v1_relat_1(k4_relat_1(A_211)) | ~v1_relat_1(A_211))), inference(superposition, [status(thm), theory('equality')], [c_2001, c_14])).
% 5.33/2.02  tff(c_3549, plain, (![B_213, A_214]: (k9_relat_1(k4_relat_1(B_213), A_214)=k1_relat_1(k8_relat_1(A_214, B_213)) | ~v1_relat_1(k4_relat_1(B_213)) | ~v1_relat_1(B_213))), inference(resolution, [status(thm)], [c_4, c_3530])).
% 5.33/2.02  tff(c_3579, plain, (![A_215, A_216]: (k9_relat_1(k4_relat_1(A_215), A_216)=k1_relat_1(k8_relat_1(A_216, A_215)) | ~v1_relat_1(A_215))), inference(resolution, [status(thm)], [c_2, c_3549])).
% 5.33/2.02  tff(c_38, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.33/2.02  tff(c_144, plain, (![B_42, A_43]: (k3_xboole_0(k1_relat_1(B_42), A_43)=k1_relat_1(k7_relat_1(B_42, A_43)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.33/2.02  tff(c_156, plain, (![A_17, A_43]: (k1_relat_1(k7_relat_1(k6_relat_1(A_17), A_43))=k3_xboole_0(A_17, A_43) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_144])).
% 5.33/2.02  tff(c_160, plain, (![A_17, A_43]: (k1_relat_1(k7_relat_1(k6_relat_1(A_17), A_43))=k3_xboole_0(A_17, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_156])).
% 5.33/2.02  tff(c_190, plain, (![B_50, A_51]: (k1_relat_1(k7_relat_1(B_50, A_51))=A_51 | ~r1_tarski(A_51, k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.33/2.02  tff(c_199, plain, (![A_17, A_51]: (k1_relat_1(k7_relat_1(k6_relat_1(A_17), A_51))=A_51 | ~r1_tarski(A_51, A_17) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_190])).
% 5.33/2.02  tff(c_220, plain, (![A_52, A_53]: (k3_xboole_0(A_52, A_53)=A_53 | ~r1_tarski(A_53, A_52))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_160, c_199])).
% 5.33/2.02  tff(c_224, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_38, c_220])).
% 5.33/2.02  tff(c_458, plain, (![B_70, A_71]: (r1_tarski(k3_xboole_0(k1_relat_1(B_70), A_71), k9_relat_1(k4_relat_1(B_70), k9_relat_1(B_70, A_71))) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.33/2.02  tff(c_476, plain, (r1_tarski('#skF_1', k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_224, c_458])).
% 5.33/2.02  tff(c_497, plain, (r1_tarski('#skF_1', k9_relat_1(k4_relat_1('#skF_2'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_476])).
% 5.33/2.02  tff(c_3618, plain, (r1_tarski('#skF_1', k1_relat_1(k8_relat_1(k9_relat_1('#skF_2', '#skF_1'), '#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3579, c_497])).
% 5.33/2.02  tff(c_3653, plain, (r1_tarski('#skF_1', k1_relat_1(k8_relat_1(k9_relat_1('#skF_2', '#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3618])).
% 5.33/2.02  tff(c_3671, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_302, c_3653])).
% 5.33/2.02  tff(c_3675, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_3671])).
% 5.33/2.02  tff(c_3677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_3675])).
% 5.33/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.02  
% 5.33/2.02  Inference rules
% 5.33/2.02  ----------------------
% 5.33/2.02  #Ref     : 0
% 5.33/2.02  #Sup     : 905
% 5.33/2.02  #Fact    : 0
% 5.33/2.02  #Define  : 0
% 5.33/2.02  #Split   : 1
% 5.33/2.02  #Chain   : 0
% 5.33/2.02  #Close   : 0
% 5.33/2.02  
% 5.33/2.02  Ordering : KBO
% 5.33/2.02  
% 5.33/2.02  Simplification rules
% 5.33/2.02  ----------------------
% 5.33/2.02  #Subsume      : 41
% 5.33/2.02  #Demod        : 1073
% 5.33/2.03  #Tautology    : 305
% 5.33/2.03  #SimpNegUnit  : 1
% 5.33/2.03  #BackRed      : 7
% 5.33/2.03  
% 5.33/2.03  #Partial instantiations: 0
% 5.33/2.03  #Strategies tried      : 1
% 5.33/2.03  
% 5.33/2.03  Timing (in seconds)
% 5.33/2.03  ----------------------
% 5.33/2.03  Preprocessing        : 0.32
% 5.33/2.03  Parsing              : 0.18
% 5.33/2.03  CNF conversion       : 0.02
% 5.33/2.03  Main loop            : 0.91
% 5.33/2.03  Inferencing          : 0.31
% 5.33/2.03  Reduction            : 0.35
% 5.33/2.03  Demodulation         : 0.27
% 5.33/2.03  BG Simplification    : 0.05
% 5.33/2.03  Subsumption          : 0.15
% 5.33/2.03  Abstraction          : 0.06
% 5.33/2.03  MUC search           : 0.00
% 5.33/2.03  Cooper               : 0.00
% 5.33/2.03  Total                : 1.26
% 5.33/2.03  Index Insertion      : 0.00
% 5.33/2.03  Index Deletion       : 0.00
% 5.33/2.03  Index Matching       : 0.00
% 5.33/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
