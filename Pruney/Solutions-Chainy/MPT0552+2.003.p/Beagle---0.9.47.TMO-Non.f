%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:57 EST 2020

% Result     : Timeout 59.05s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   95 ( 327 expanded)
%              Number of leaves         :   35 ( 118 expanded)
%              Depth                    :   17
%              Number of atoms          :  158 ( 740 expanded)
%              Number of equality atoms :   23 ( 114 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [B_40,A_39] :
      ( k2_relat_1(k7_relat_1(B_40,A_39)) = k9_relat_1(B_40,A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_240,plain,(
    ! [B_81,A_82] :
      ( k3_xboole_0(k2_relat_1(B_81),A_82) = k2_relat_1(k8_relat_1(A_82,B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_255,plain,(
    ! [A_82,B_40,A_39] :
      ( k2_relat_1(k8_relat_1(A_82,k7_relat_1(B_40,A_39))) = k3_xboole_0(k9_relat_1(B_40,A_39),A_82)
      | ~ v1_relat_1(k7_relat_1(B_40,A_39))
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_240])).

tff(c_330,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k2_relat_1(A_94),k2_relat_1(B_95))
      | ~ r1_tarski(A_94,B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1340,plain,(
    ! [B_163,A_164,B_165] :
      ( r1_tarski(k9_relat_1(B_163,A_164),k2_relat_1(B_165))
      | ~ r1_tarski(k7_relat_1(B_163,A_164),B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(k7_relat_1(B_163,A_164))
      | ~ v1_relat_1(B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_330])).

tff(c_108621,plain,(
    ! [B_1156,A_1155,A_1159,B_1157,A_1158] :
      ( r1_tarski(k9_relat_1(B_1156,A_1158),k3_xboole_0(k9_relat_1(B_1157,A_1155),A_1159))
      | ~ r1_tarski(k7_relat_1(B_1156,A_1158),k8_relat_1(A_1159,k7_relat_1(B_1157,A_1155)))
      | ~ v1_relat_1(k8_relat_1(A_1159,k7_relat_1(B_1157,A_1155)))
      | ~ v1_relat_1(k7_relat_1(B_1156,A_1158))
      | ~ v1_relat_1(B_1156)
      | ~ v1_relat_1(k7_relat_1(B_1157,A_1155))
      | ~ v1_relat_1(B_1157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_1340])).

tff(c_46,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_108648,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1')))
    | ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108621,c_46])).

tff(c_109181,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1')))
    | ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_108648])).

tff(c_109182,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_109181])).

tff(c_109185,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_109182])).

tff(c_109189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_109185])).

tff(c_109191,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_109181])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k8_relat_1(A_23,B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [B_63,A_64] : k1_setfam_1(k2_tarski(B_63,A_64)) = k3_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_86])).

tff(c_16,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    ! [B_63,A_64] : k3_xboole_0(B_63,A_64) = k3_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_16])).

tff(c_28,plain,(
    ! [C_27,A_25,B_26] :
      ( k7_relat_1(k7_relat_1(C_27,A_25),B_26) = k7_relat_1(C_27,k3_xboole_0(A_25,B_26))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_432,plain,(
    ! [B_106,A_107,C_108] :
      ( r1_tarski(k7_relat_1(B_106,A_107),k7_relat_1(C_108,A_107))
      | ~ r1_tarski(B_106,C_108)
      | ~ v1_relat_1(C_108)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2709,plain,(
    ! [C_222,A_223,B_224,C_225] :
      ( r1_tarski(k7_relat_1(C_222,k3_xboole_0(A_223,B_224)),k7_relat_1(C_225,B_224))
      | ~ r1_tarski(k7_relat_1(C_222,A_223),C_225)
      | ~ v1_relat_1(C_225)
      | ~ v1_relat_1(k7_relat_1(C_222,A_223))
      | ~ v1_relat_1(C_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_432])).

tff(c_2778,plain,(
    ! [C_222,B_63,A_64,C_225] :
      ( r1_tarski(k7_relat_1(C_222,k3_xboole_0(B_63,A_64)),k7_relat_1(C_225,B_63))
      | ~ r1_tarski(k7_relat_1(C_222,A_64),C_225)
      | ~ v1_relat_1(C_225)
      | ~ v1_relat_1(k7_relat_1(C_222,A_64))
      | ~ v1_relat_1(C_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_2709])).

tff(c_36,plain,(
    ! [A_36,C_38,B_37] :
      ( k8_relat_1(A_36,k7_relat_1(C_38,B_37)) = k7_relat_1(k8_relat_1(A_36,C_38),B_37)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_109190,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_109181])).

tff(c_113149,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_109190])).

tff(c_113152,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3'),'#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_113149])).

tff(c_113154,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_113152])).

tff(c_113157,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_2'),k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3'))
    | ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2778,c_113154])).

tff(c_113160,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_2'),k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3'))
    | ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_113157])).

tff(c_113161,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_113160])).

tff(c_113164,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_113161])).

tff(c_113168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_113164])).

tff(c_113170,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_113160])).

tff(c_310,plain,(
    ! [A_91,C_92,B_93] :
      ( k8_relat_1(A_91,k7_relat_1(C_92,B_93)) = k7_relat_1(k8_relat_1(A_91,C_92),B_93)
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_216,plain,(
    ! [A_78,B_79] :
      ( k8_relat_1(A_78,B_79) = B_79
      | ~ r1_tarski(k2_relat_1(B_79),A_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_224,plain,(
    ! [B_79] :
      ( k8_relat_1(k2_relat_1(B_79),B_79) = B_79
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_895,plain,(
    ! [C_137,B_138] :
      ( k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(C_137,B_138)),C_137),B_138) = k7_relat_1(C_137,B_138)
      | ~ v1_relat_1(k7_relat_1(C_137,B_138))
      | ~ v1_relat_1(C_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_224])).

tff(c_1241,plain,(
    ! [B_158,A_159] :
      ( k7_relat_1(k8_relat_1(k9_relat_1(B_158,A_159),B_158),A_159) = k7_relat_1(B_158,A_159)
      | ~ v1_relat_1(k7_relat_1(B_158,A_159))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(B_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_895])).

tff(c_44,plain,(
    ! [B_45,A_44] :
      ( r1_tarski(k7_relat_1(B_45,A_44),B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1311,plain,(
    ! [B_158,A_159] :
      ( r1_tarski(k7_relat_1(B_158,A_159),k8_relat_1(k9_relat_1(B_158,A_159),B_158))
      | ~ v1_relat_1(k8_relat_1(k9_relat_1(B_158,A_159),B_158))
      | ~ v1_relat_1(k7_relat_1(B_158,A_159))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(B_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_44])).

tff(c_113169,plain,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_2'),k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_113160])).

tff(c_113818,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_2'),k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_113169])).

tff(c_113824,plain,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1311,c_113818])).

tff(c_113830,plain,(
    ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_113170,c_113824])).

tff(c_113833,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_113830])).

tff(c_113837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_113833])).

tff(c_113838,plain,(
    ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_113169])).

tff(c_113842,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_113838])).

tff(c_113846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_113842])).

tff(c_113847,plain,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_109190])).

tff(c_113944,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_113847])).

tff(c_113947,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_113944])).

tff(c_113951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_113947])).

tff(c_113952,plain,(
    ~ v1_relat_1(k8_relat_1(k9_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_113847])).

tff(c_114606,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_113952])).

tff(c_114612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109191,c_114606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 59.05/32.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.05/32.79  
% 59.05/32.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.05/32.79  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 59.05/32.79  
% 59.05/32.79  %Foreground sorts:
% 59.05/32.79  
% 59.05/32.79  
% 59.05/32.79  %Background operators:
% 59.05/32.79  
% 59.05/32.79  
% 59.05/32.79  %Foreground operators:
% 59.05/32.79  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 59.05/32.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 59.05/32.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 59.05/32.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 59.05/32.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 59.05/32.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 59.05/32.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 59.05/32.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 59.05/32.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 59.05/32.79  tff('#skF_2', type, '#skF_2': $i).
% 59.05/32.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 59.05/32.79  tff('#skF_3', type, '#skF_3': $i).
% 59.05/32.79  tff('#skF_1', type, '#skF_1': $i).
% 59.05/32.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 59.05/32.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 59.05/32.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 59.05/32.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 59.05/32.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 59.05/32.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 59.05/32.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 59.05/32.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 59.05/32.79  
% 59.05/32.80  tff(f_111, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 59.05/32.80  tff(f_56, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 59.05/32.80  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 59.05/32.80  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 59.05/32.80  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 59.05/32.80  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 59.05/32.80  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 59.05/32.80  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 59.05/32.80  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 59.05/32.80  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 59.05/32.80  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 59.05/32.80  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 59.05/32.80  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 59.05/32.80  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 59.05/32.80  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 59.05/32.80  tff(c_24, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 59.05/32.80  tff(c_38, plain, (![B_40, A_39]: (k2_relat_1(k7_relat_1(B_40, A_39))=k9_relat_1(B_40, A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_91])).
% 59.05/32.80  tff(c_240, plain, (![B_81, A_82]: (k3_xboole_0(k2_relat_1(B_81), A_82)=k2_relat_1(k8_relat_1(A_82, B_81)) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_77])).
% 59.05/32.80  tff(c_255, plain, (![A_82, B_40, A_39]: (k2_relat_1(k8_relat_1(A_82, k7_relat_1(B_40, A_39)))=k3_xboole_0(k9_relat_1(B_40, A_39), A_82) | ~v1_relat_1(k7_relat_1(B_40, A_39)) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_38, c_240])).
% 59.05/32.80  tff(c_330, plain, (![A_94, B_95]: (r1_tarski(k2_relat_1(A_94), k2_relat_1(B_95)) | ~r1_tarski(A_94, B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_102])).
% 59.05/32.80  tff(c_1340, plain, (![B_163, A_164, B_165]: (r1_tarski(k9_relat_1(B_163, A_164), k2_relat_1(B_165)) | ~r1_tarski(k7_relat_1(B_163, A_164), B_165) | ~v1_relat_1(B_165) | ~v1_relat_1(k7_relat_1(B_163, A_164)) | ~v1_relat_1(B_163))), inference(superposition, [status(thm), theory('equality')], [c_38, c_330])).
% 59.05/32.80  tff(c_108621, plain, (![B_1156, A_1155, A_1159, B_1157, A_1158]: (r1_tarski(k9_relat_1(B_1156, A_1158), k3_xboole_0(k9_relat_1(B_1157, A_1155), A_1159)) | ~r1_tarski(k7_relat_1(B_1156, A_1158), k8_relat_1(A_1159, k7_relat_1(B_1157, A_1155))) | ~v1_relat_1(k8_relat_1(A_1159, k7_relat_1(B_1157, A_1155))) | ~v1_relat_1(k7_relat_1(B_1156, A_1158)) | ~v1_relat_1(B_1156) | ~v1_relat_1(k7_relat_1(B_1157, A_1155)) | ~v1_relat_1(B_1157))), inference(superposition, [status(thm), theory('equality')], [c_255, c_1340])).
% 59.05/32.80  tff(c_46, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 59.05/32.80  tff(c_108648, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1'))) | ~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108621, c_46])).
% 59.05/32.80  tff(c_109181, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1'))) | ~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_108648])).
% 59.05/32.80  tff(c_109182, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_109181])).
% 59.05/32.80  tff(c_109185, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_109182])).
% 59.05/32.80  tff(c_109189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_109185])).
% 59.05/32.80  tff(c_109191, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_109181])).
% 59.05/32.80  tff(c_26, plain, (![A_23, B_24]: (v1_relat_1(k8_relat_1(A_23, B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 59.05/32.80  tff(c_8, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 59.05/32.80  tff(c_86, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 59.05/32.80  tff(c_117, plain, (![B_63, A_64]: (k1_setfam_1(k2_tarski(B_63, A_64))=k3_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_8, c_86])).
% 59.05/32.80  tff(c_16, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 59.05/32.80  tff(c_123, plain, (![B_63, A_64]: (k3_xboole_0(B_63, A_64)=k3_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_117, c_16])).
% 59.05/32.80  tff(c_28, plain, (![C_27, A_25, B_26]: (k7_relat_1(k7_relat_1(C_27, A_25), B_26)=k7_relat_1(C_27, k3_xboole_0(A_25, B_26)) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 59.05/32.80  tff(c_432, plain, (![B_106, A_107, C_108]: (r1_tarski(k7_relat_1(B_106, A_107), k7_relat_1(C_108, A_107)) | ~r1_tarski(B_106, C_108) | ~v1_relat_1(C_108) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_73])).
% 59.05/32.80  tff(c_2709, plain, (![C_222, A_223, B_224, C_225]: (r1_tarski(k7_relat_1(C_222, k3_xboole_0(A_223, B_224)), k7_relat_1(C_225, B_224)) | ~r1_tarski(k7_relat_1(C_222, A_223), C_225) | ~v1_relat_1(C_225) | ~v1_relat_1(k7_relat_1(C_222, A_223)) | ~v1_relat_1(C_222))), inference(superposition, [status(thm), theory('equality')], [c_28, c_432])).
% 59.05/32.80  tff(c_2778, plain, (![C_222, B_63, A_64, C_225]: (r1_tarski(k7_relat_1(C_222, k3_xboole_0(B_63, A_64)), k7_relat_1(C_225, B_63)) | ~r1_tarski(k7_relat_1(C_222, A_64), C_225) | ~v1_relat_1(C_225) | ~v1_relat_1(k7_relat_1(C_222, A_64)) | ~v1_relat_1(C_222))), inference(superposition, [status(thm), theory('equality')], [c_123, c_2709])).
% 59.05/32.80  tff(c_36, plain, (![A_36, C_38, B_37]: (k8_relat_1(A_36, k7_relat_1(C_38, B_37))=k7_relat_1(k8_relat_1(A_36, C_38), B_37) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_87])).
% 59.05/32.80  tff(c_109190, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_109181])).
% 59.05/32.80  tff(c_113149, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1')))), inference(splitLeft, [status(thm)], [c_109190])).
% 59.05/32.80  tff(c_113152, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3'), '#skF_1')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_113149])).
% 59.05/32.80  tff(c_113154, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_113152])).
% 59.05/32.80  tff(c_113157, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3')) | ~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2778, c_113154])).
% 59.05/32.80  tff(c_113160, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3')) | ~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_113157])).
% 59.05/32.80  tff(c_113161, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_113160])).
% 59.05/32.80  tff(c_113164, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_113161])).
% 59.05/32.80  tff(c_113168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_113164])).
% 59.05/32.80  tff(c_113170, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_113160])).
% 59.05/32.80  tff(c_310, plain, (![A_91, C_92, B_93]: (k8_relat_1(A_91, k7_relat_1(C_92, B_93))=k7_relat_1(k8_relat_1(A_91, C_92), B_93) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_87])).
% 59.05/32.80  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 59.05/32.80  tff(c_216, plain, (![A_78, B_79]: (k8_relat_1(A_78, B_79)=B_79 | ~r1_tarski(k2_relat_1(B_79), A_78) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_83])).
% 59.05/32.80  tff(c_224, plain, (![B_79]: (k8_relat_1(k2_relat_1(B_79), B_79)=B_79 | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_6, c_216])).
% 59.05/32.80  tff(c_895, plain, (![C_137, B_138]: (k7_relat_1(k8_relat_1(k2_relat_1(k7_relat_1(C_137, B_138)), C_137), B_138)=k7_relat_1(C_137, B_138) | ~v1_relat_1(k7_relat_1(C_137, B_138)) | ~v1_relat_1(C_137))), inference(superposition, [status(thm), theory('equality')], [c_310, c_224])).
% 59.05/32.80  tff(c_1241, plain, (![B_158, A_159]: (k7_relat_1(k8_relat_1(k9_relat_1(B_158, A_159), B_158), A_159)=k7_relat_1(B_158, A_159) | ~v1_relat_1(k7_relat_1(B_158, A_159)) | ~v1_relat_1(B_158) | ~v1_relat_1(B_158))), inference(superposition, [status(thm), theory('equality')], [c_38, c_895])).
% 59.05/32.80  tff(c_44, plain, (![B_45, A_44]: (r1_tarski(k7_relat_1(B_45, A_44), B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_106])).
% 59.05/32.80  tff(c_1311, plain, (![B_158, A_159]: (r1_tarski(k7_relat_1(B_158, A_159), k8_relat_1(k9_relat_1(B_158, A_159), B_158)) | ~v1_relat_1(k8_relat_1(k9_relat_1(B_158, A_159), B_158)) | ~v1_relat_1(k7_relat_1(B_158, A_159)) | ~v1_relat_1(B_158) | ~v1_relat_1(B_158))), inference(superposition, [status(thm), theory('equality')], [c_1241, c_44])).
% 59.05/32.80  tff(c_113169, plain, (~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_113160])).
% 59.05/32.80  tff(c_113818, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_113169])).
% 59.05/32.80  tff(c_113824, plain, (~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1311, c_113818])).
% 59.05/32.80  tff(c_113830, plain, (~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_113170, c_113824])).
% 59.05/32.80  tff(c_113833, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_113830])).
% 59.05/32.80  tff(c_113837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_113833])).
% 59.05/32.80  tff(c_113838, plain, (~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_113169])).
% 59.05/32.80  tff(c_113842, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_113838])).
% 59.05/32.80  tff(c_113846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_113842])).
% 59.05/32.80  tff(c_113847, plain, (~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_109190])).
% 59.05/32.80  tff(c_113944, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_113847])).
% 59.05/32.80  tff(c_113947, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_113944])).
% 59.05/32.80  tff(c_113951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_113947])).
% 59.05/32.80  tff(c_113952, plain, (~v1_relat_1(k8_relat_1(k9_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_113847])).
% 59.05/32.80  tff(c_114606, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_113952])).
% 59.05/32.80  tff(c_114612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109191, c_114606])).
% 59.05/32.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.05/32.80  
% 59.05/32.80  Inference rules
% 59.05/32.80  ----------------------
% 59.05/32.80  #Ref     : 0
% 59.05/32.80  #Sup     : 34151
% 59.05/32.80  #Fact    : 0
% 59.05/32.80  #Define  : 0
% 59.05/32.80  #Split   : 5
% 59.05/32.80  #Chain   : 0
% 59.05/32.80  #Close   : 0
% 59.05/32.80  
% 59.05/32.80  Ordering : KBO
% 59.05/32.80  
% 59.05/32.80  Simplification rules
% 59.05/32.80  ----------------------
% 59.05/32.80  #Subsume      : 2485
% 59.05/32.80  #Demod        : 679
% 59.05/32.80  #Tautology    : 661
% 59.05/32.80  #SimpNegUnit  : 0
% 59.05/32.80  #BackRed      : 0
% 59.05/32.80  
% 59.05/32.80  #Partial instantiations: 0
% 59.05/32.80  #Strategies tried      : 1
% 59.05/32.80  
% 59.05/32.80  Timing (in seconds)
% 59.05/32.80  ----------------------
% 59.05/32.81  Preprocessing        : 0.33
% 59.05/32.81  Parsing              : 0.17
% 59.05/32.81  CNF conversion       : 0.02
% 59.05/32.81  Main loop            : 31.71
% 59.05/32.81  Inferencing          : 5.93
% 59.05/32.81  Reduction            : 5.66
% 59.05/32.81  Demodulation         : 4.52
% 59.05/32.81  BG Simplification    : 3.11
% 59.05/32.81  Subsumption          : 15.67
% 59.05/32.81  Abstraction          : 1.29
% 59.05/32.81  MUC search           : 0.00
% 59.05/32.81  Cooper               : 0.00
% 59.05/32.81  Total                : 32.07
% 59.05/32.81  Index Insertion      : 0.00
% 59.05/32.81  Index Deletion       : 0.00
% 59.05/32.81  Index Matching       : 0.00
% 59.05/32.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
