%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:01 EST 2020

% Result     : Theorem 8.33s
% Output     : CNFRefutation 8.33s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 183 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 391 expanded)
%              Number of equality atoms :   48 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_93,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_222,plain,(
    ! [A_52] :
      ( k4_relat_1(A_52) = k2_funct_1(A_52)
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_228,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_222])).

tff(c_234,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_228])).

tff(c_18,plain,(
    ! [A_18] :
      ( k1_relat_1(k4_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_241,plain,
    ( k1_relat_1(k2_funct_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_18])).

tff(c_247,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_241])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k10_relat_1(B_10,A_9),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_284,plain,(
    ! [A_9] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_2'),A_9),k2_relat_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_10])).

tff(c_304,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_307,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_307])).

tff(c_313,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_30,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ! [B_26,A_25] : k5_relat_1(k6_relat_1(B_26),k6_relat_1(A_25)) = k6_relat_1(k3_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_355,plain,(
    ! [A_61,B_62] :
      ( k10_relat_1(A_61,k1_relat_1(B_62)) = k1_relat_1(k5_relat_1(A_61,B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_381,plain,(
    ! [A_61,A_19] :
      ( k1_relat_1(k5_relat_1(A_61,k6_relat_1(A_19))) = k10_relat_1(A_61,A_19)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_355])).

tff(c_434,plain,(
    ! [A_70,A_71] :
      ( k1_relat_1(k5_relat_1(A_70,k6_relat_1(A_71))) = k10_relat_1(A_70,A_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_381])).

tff(c_456,plain,(
    ! [A_25,B_26] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_25,B_26))) = k10_relat_1(k6_relat_1(B_26),A_25)
      | ~ v1_relat_1(k6_relat_1(B_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_434])).

tff(c_462,plain,(
    ! [B_26,A_25] : k10_relat_1(k6_relat_1(B_26),A_25) = k3_xboole_0(A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_20,c_456])).

tff(c_40,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k2_funct_1(A_27)) = k6_relat_1(k1_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_859,plain,(
    ! [B_92,C_93,A_94] :
      ( k10_relat_1(k5_relat_1(B_92,C_93),A_94) = k10_relat_1(B_92,k10_relat_1(C_93,A_94))
      | ~ v1_relat_1(C_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_875,plain,(
    ! [A_27,A_94] :
      ( k10_relat_1(k6_relat_1(k1_relat_1(A_27)),A_94) = k10_relat_1(A_27,k10_relat_1(k2_funct_1(A_27),A_94))
      | ~ v1_relat_1(k2_funct_1(A_27))
      | ~ v1_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_859])).

tff(c_9742,plain,(
    ! [A_247,A_248] :
      ( k10_relat_1(A_247,k10_relat_1(k2_funct_1(A_247),A_248)) = k3_xboole_0(A_248,k1_relat_1(A_247))
      | ~ v1_relat_1(k2_funct_1(A_247))
      | ~ v1_relat_1(A_247)
      | ~ v2_funct_1(A_247)
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_875])).

tff(c_146,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k10_relat_1(B_42,A_43),k1_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_149,plain,(
    ! [A_18,A_43] :
      ( r1_tarski(k10_relat_1(k4_relat_1(A_18),A_43),k2_relat_1(A_18))
      | ~ v1_relat_1(k4_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_146])).

tff(c_1118,plain,(
    ! [B_111,A_112] :
      ( k9_relat_1(B_111,k10_relat_1(B_111,A_112)) = A_112
      | ~ r1_tarski(A_112,k2_relat_1(B_111))
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9394,plain,(
    ! [A_239,A_240] :
      ( k9_relat_1(A_239,k10_relat_1(A_239,k10_relat_1(k4_relat_1(A_239),A_240))) = k10_relat_1(k4_relat_1(A_239),A_240)
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(k4_relat_1(A_239))
      | ~ v1_relat_1(A_239) ) ),
    inference(resolution,[status(thm)],[c_149,c_1118])).

tff(c_9439,plain,(
    ! [A_240] :
      ( k9_relat_1('#skF_2',k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),A_240))) = k10_relat_1(k4_relat_1('#skF_2'),A_240)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1(k4_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_9394])).

tff(c_9451,plain,(
    ! [A_240] : k9_relat_1('#skF_2',k10_relat_1('#skF_2',k10_relat_1(k2_funct_1('#skF_2'),A_240))) = k10_relat_1(k2_funct_1('#skF_2'),A_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_313,c_234,c_46,c_234,c_9439])).

tff(c_9757,plain,(
    ! [A_248] :
      ( k9_relat_1('#skF_2',k3_xboole_0(A_248,k1_relat_1('#skF_2'))) = k10_relat_1(k2_funct_1('#skF_2'),A_248)
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9742,c_9451])).

tff(c_10168,plain,(
    ! [A_250] : k9_relat_1('#skF_2',k3_xboole_0(A_250,k1_relat_1('#skF_2'))) = k10_relat_1(k2_funct_1('#skF_2'),A_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_48,c_313,c_9757])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_120,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(B_47,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_120])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [B_47,A_46] : k3_xboole_0(B_47,A_46) = k3_xboole_0(A_46,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_6])).

tff(c_253,plain,(
    ! [B_53,A_54] :
      ( k9_relat_1(B_53,k3_xboole_0(k1_relat_1(B_53),A_54)) = k9_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_263,plain,(
    ! [B_53,B_47] :
      ( k9_relat_1(B_53,k3_xboole_0(B_47,k1_relat_1(B_53))) = k9_relat_1(B_53,B_47)
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_253])).

tff(c_10174,plain,(
    ! [A_250] :
      ( k10_relat_1(k2_funct_1('#skF_2'),A_250) = k9_relat_1('#skF_2',A_250)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10168,c_263])).

tff(c_10223,plain,(
    ! [A_250] : k10_relat_1(k2_funct_1('#skF_2'),A_250) = k9_relat_1('#skF_2',A_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10174])).

tff(c_42,plain,(
    k10_relat_1(k2_funct_1('#skF_2'),'#skF_1') != k9_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10223,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.33/3.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/3.35  
% 8.33/3.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/3.36  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.33/3.36  
% 8.33/3.36  %Foreground sorts:
% 8.33/3.36  
% 8.33/3.36  
% 8.33/3.36  %Background operators:
% 8.33/3.36  
% 8.33/3.36  
% 8.33/3.36  %Foreground operators:
% 8.33/3.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.33/3.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.33/3.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.33/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.33/3.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.33/3.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.33/3.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.33/3.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.33/3.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.33/3.36  tff('#skF_2', type, '#skF_2': $i).
% 8.33/3.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.33/3.36  tff('#skF_1', type, '#skF_1': $i).
% 8.33/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.33/3.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.33/3.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.33/3.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.33/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.33/3.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.33/3.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.33/3.36  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.33/3.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.33/3.36  
% 8.33/3.37  tff(f_112, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 8.33/3.37  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.33/3.37  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.33/3.37  tff(f_59, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 8.33/3.37  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 8.33/3.37  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.33/3.37  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.33/3.37  tff(f_93, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 8.33/3.37  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 8.33/3.37  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 8.33/3.37  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 8.33/3.37  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 8.33/3.37  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.33/3.37  tff(f_31, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.33/3.37  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 8.33/3.37  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.33/3.37  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.33/3.37  tff(c_44, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.33/3.37  tff(c_28, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.33/3.37  tff(c_222, plain, (![A_52]: (k4_relat_1(A_52)=k2_funct_1(A_52) | ~v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.33/3.37  tff(c_228, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_222])).
% 8.33/3.37  tff(c_234, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_228])).
% 8.33/3.37  tff(c_18, plain, (![A_18]: (k1_relat_1(k4_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.33/3.37  tff(c_241, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_234, c_18])).
% 8.33/3.37  tff(c_247, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_241])).
% 8.33/3.37  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k10_relat_1(B_10, A_9), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.33/3.37  tff(c_284, plain, (![A_9]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_2'), A_9), k2_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_247, c_10])).
% 8.33/3.37  tff(c_304, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_284])).
% 8.33/3.37  tff(c_307, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_304])).
% 8.33/3.37  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_307])).
% 8.33/3.37  tff(c_313, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_284])).
% 8.33/3.37  tff(c_30, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.33/3.37  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.33/3.37  tff(c_36, plain, (![B_26, A_25]: (k5_relat_1(k6_relat_1(B_26), k6_relat_1(A_25))=k6_relat_1(k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.33/3.37  tff(c_355, plain, (![A_61, B_62]: (k10_relat_1(A_61, k1_relat_1(B_62))=k1_relat_1(k5_relat_1(A_61, B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.33/3.37  tff(c_381, plain, (![A_61, A_19]: (k1_relat_1(k5_relat_1(A_61, k6_relat_1(A_19)))=k10_relat_1(A_61, A_19) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_61))), inference(superposition, [status(thm), theory('equality')], [c_20, c_355])).
% 8.33/3.37  tff(c_434, plain, (![A_70, A_71]: (k1_relat_1(k5_relat_1(A_70, k6_relat_1(A_71)))=k10_relat_1(A_70, A_71) | ~v1_relat_1(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_381])).
% 8.33/3.37  tff(c_456, plain, (![A_25, B_26]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_25, B_26)))=k10_relat_1(k6_relat_1(B_26), A_25) | ~v1_relat_1(k6_relat_1(B_26)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_434])).
% 8.33/3.37  tff(c_462, plain, (![B_26, A_25]: (k10_relat_1(k6_relat_1(B_26), A_25)=k3_xboole_0(A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_20, c_456])).
% 8.33/3.37  tff(c_40, plain, (![A_27]: (k5_relat_1(A_27, k2_funct_1(A_27))=k6_relat_1(k1_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.33/3.37  tff(c_859, plain, (![B_92, C_93, A_94]: (k10_relat_1(k5_relat_1(B_92, C_93), A_94)=k10_relat_1(B_92, k10_relat_1(C_93, A_94)) | ~v1_relat_1(C_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.33/3.37  tff(c_875, plain, (![A_27, A_94]: (k10_relat_1(k6_relat_1(k1_relat_1(A_27)), A_94)=k10_relat_1(A_27, k10_relat_1(k2_funct_1(A_27), A_94)) | ~v1_relat_1(k2_funct_1(A_27)) | ~v1_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_40, c_859])).
% 8.33/3.37  tff(c_9742, plain, (![A_247, A_248]: (k10_relat_1(A_247, k10_relat_1(k2_funct_1(A_247), A_248))=k3_xboole_0(A_248, k1_relat_1(A_247)) | ~v1_relat_1(k2_funct_1(A_247)) | ~v1_relat_1(A_247) | ~v2_funct_1(A_247) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_875])).
% 8.33/3.37  tff(c_146, plain, (![B_42, A_43]: (r1_tarski(k10_relat_1(B_42, A_43), k1_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.33/3.37  tff(c_149, plain, (![A_18, A_43]: (r1_tarski(k10_relat_1(k4_relat_1(A_18), A_43), k2_relat_1(A_18)) | ~v1_relat_1(k4_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_18, c_146])).
% 8.33/3.37  tff(c_1118, plain, (![B_111, A_112]: (k9_relat_1(B_111, k10_relat_1(B_111, A_112))=A_112 | ~r1_tarski(A_112, k2_relat_1(B_111)) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.33/3.37  tff(c_9394, plain, (![A_239, A_240]: (k9_relat_1(A_239, k10_relat_1(A_239, k10_relat_1(k4_relat_1(A_239), A_240)))=k10_relat_1(k4_relat_1(A_239), A_240) | ~v1_funct_1(A_239) | ~v1_relat_1(k4_relat_1(A_239)) | ~v1_relat_1(A_239))), inference(resolution, [status(thm)], [c_149, c_1118])).
% 8.33/3.37  tff(c_9439, plain, (![A_240]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), A_240)))=k10_relat_1(k4_relat_1('#skF_2'), A_240) | ~v1_funct_1('#skF_2') | ~v1_relat_1(k4_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_9394])).
% 8.33/3.37  tff(c_9451, plain, (![A_240]: (k9_relat_1('#skF_2', k10_relat_1('#skF_2', k10_relat_1(k2_funct_1('#skF_2'), A_240)))=k10_relat_1(k2_funct_1('#skF_2'), A_240))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_313, c_234, c_46, c_234, c_9439])).
% 8.33/3.37  tff(c_9757, plain, (![A_248]: (k9_relat_1('#skF_2', k3_xboole_0(A_248, k1_relat_1('#skF_2')))=k10_relat_1(k2_funct_1('#skF_2'), A_248) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9742, c_9451])).
% 8.33/3.37  tff(c_10168, plain, (![A_250]: (k9_relat_1('#skF_2', k3_xboole_0(A_250, k1_relat_1('#skF_2')))=k10_relat_1(k2_funct_1('#skF_2'), A_250))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_48, c_313, c_9757])).
% 8.33/3.37  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.33/3.37  tff(c_120, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.33/3.37  tff(c_156, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(B_47, A_46))), inference(superposition, [status(thm), theory('equality')], [c_2, c_120])).
% 8.33/3.37  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.33/3.37  tff(c_162, plain, (![B_47, A_46]: (k3_xboole_0(B_47, A_46)=k3_xboole_0(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_156, c_6])).
% 8.33/3.37  tff(c_253, plain, (![B_53, A_54]: (k9_relat_1(B_53, k3_xboole_0(k1_relat_1(B_53), A_54))=k9_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.33/3.37  tff(c_263, plain, (![B_53, B_47]: (k9_relat_1(B_53, k3_xboole_0(B_47, k1_relat_1(B_53)))=k9_relat_1(B_53, B_47) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_162, c_253])).
% 8.33/3.37  tff(c_10174, plain, (![A_250]: (k10_relat_1(k2_funct_1('#skF_2'), A_250)=k9_relat_1('#skF_2', A_250) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10168, c_263])).
% 8.33/3.37  tff(c_10223, plain, (![A_250]: (k10_relat_1(k2_funct_1('#skF_2'), A_250)=k9_relat_1('#skF_2', A_250))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10174])).
% 8.33/3.37  tff(c_42, plain, (k10_relat_1(k2_funct_1('#skF_2'), '#skF_1')!=k9_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.33/3.37  tff(c_10239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10223, c_42])).
% 8.33/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/3.37  
% 8.33/3.37  Inference rules
% 8.33/3.37  ----------------------
% 8.33/3.37  #Ref     : 0
% 8.33/3.37  #Sup     : 2493
% 8.33/3.37  #Fact    : 0
% 8.33/3.37  #Define  : 0
% 8.33/3.37  #Split   : 4
% 8.33/3.37  #Chain   : 0
% 8.33/3.37  #Close   : 0
% 8.33/3.37  
% 8.33/3.37  Ordering : KBO
% 8.33/3.37  
% 8.33/3.37  Simplification rules
% 8.33/3.37  ----------------------
% 8.33/3.37  #Subsume      : 175
% 8.33/3.37  #Demod        : 2279
% 8.33/3.37  #Tautology    : 914
% 8.33/3.37  #SimpNegUnit  : 0
% 8.33/3.37  #BackRed      : 7
% 8.33/3.37  
% 8.33/3.37  #Partial instantiations: 0
% 8.33/3.37  #Strategies tried      : 1
% 8.33/3.37  
% 8.33/3.37  Timing (in seconds)
% 8.33/3.37  ----------------------
% 8.33/3.38  Preprocessing        : 0.32
% 8.33/3.38  Parsing              : 0.18
% 8.33/3.38  CNF conversion       : 0.02
% 8.33/3.38  Main loop            : 2.27
% 8.33/3.38  Inferencing          : 0.46
% 8.33/3.38  Reduction            : 1.38
% 8.33/3.38  Demodulation         : 1.27
% 8.33/3.38  BG Simplification    : 0.07
% 8.33/3.38  Subsumption          : 0.25
% 8.33/3.38  Abstraction          : 0.09
% 8.33/3.38  MUC search           : 0.00
% 8.33/3.38  Cooper               : 0.00
% 8.33/3.38  Total                : 2.63
% 8.33/3.38  Index Insertion      : 0.00
% 8.33/3.38  Index Deletion       : 0.00
% 8.33/3.38  Index Matching       : 0.00
% 8.33/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
