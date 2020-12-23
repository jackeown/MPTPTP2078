%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:23 EST 2020

% Result     : Theorem 19.29s
% Output     : CNFRefutation 19.29s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 366 expanded)
%              Number of leaves         :   39 ( 141 expanded)
%              Depth                    :   18
%              Number of atoms          :  168 ( 614 expanded)
%              Number of equality atoms :   50 ( 255 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_105,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_136,plain,(
    ! [B_62,A_63] : k1_setfam_1(k2_tarski(B_62,A_63)) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_121])).

tff(c_18,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_142,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_18])).

tff(c_34,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k7_relat_1(B_35,A_34),B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [A_31] : k1_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [A_40] : v1_relat_1(k6_relat_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_268,plain,(
    ! [B_81,A_82] : k5_relat_1(k6_relat_1(B_81),k6_relat_1(A_82)) = k6_relat_1(k3_xboole_0(A_82,B_81)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k7_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_274,plain,(
    ! [A_82,B_81] :
      ( k7_relat_1(k6_relat_1(A_82),B_81) = k6_relat_1(k3_xboole_0(A_82,B_81))
      | ~ v1_relat_1(k6_relat_1(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_36])).

tff(c_284,plain,(
    ! [A_82,B_81] : k7_relat_1(k6_relat_1(A_82),B_81) = k6_relat_1(k3_xboole_0(A_82,B_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_274])).

tff(c_391,plain,(
    ! [B_94,A_95] :
      ( k7_relat_1(B_94,A_95) = B_94
      | ~ r1_tarski(k1_relat_1(B_94),A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_400,plain,(
    ! [A_31,A_95] :
      ( k7_relat_1(k6_relat_1(A_31),A_95) = k6_relat_1(A_31)
      | ~ r1_tarski(A_31,A_95)
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_391])).

tff(c_977,plain,(
    ! [A_134,A_135] :
      ( k6_relat_1(k3_xboole_0(A_134,A_135)) = k6_relat_1(A_134)
      | ~ r1_tarski(A_134,A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_284,c_400])).

tff(c_1010,plain,(
    ! [A_134,A_135] :
      ( k3_xboole_0(A_134,A_135) = k1_relat_1(k6_relat_1(A_134))
      | ~ r1_tarski(A_134,A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_28])).

tff(c_1044,plain,(
    ! [A_136,A_137] :
      ( k3_xboole_0(A_136,A_137) = A_136
      | ~ r1_tarski(A_136,A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1010])).

tff(c_1092,plain,(
    ! [B_35,A_34] :
      ( k3_xboole_0(k7_relat_1(B_35,A_34),B_35) = k7_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_34,c_1044])).

tff(c_1117,plain,(
    ! [B_35,A_34] :
      ( k3_xboole_0(B_35,k7_relat_1(B_35,A_34)) = k7_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1092])).

tff(c_288,plain,(
    ! [A_83,B_84] : k7_relat_1(k6_relat_1(A_83),B_84) = k6_relat_1(k3_xboole_0(A_83,B_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_274])).

tff(c_32,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_33,A_32)),A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_297,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_83,B_84))),B_84)
      | ~ v1_relat_1(k6_relat_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_32])).

tff(c_330,plain,(
    ! [A_86,B_87] : r1_tarski(k3_xboole_0(A_86,B_87),B_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_297])).

tff(c_341,plain,(
    ! [B_62,A_63] : r1_tarski(k3_xboole_0(B_62,A_63),B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_330])).

tff(c_1824,plain,(
    ! [B_152,A_153] : k3_xboole_0(k3_xboole_0(B_152,A_153),B_152) = k3_xboole_0(B_152,A_153) ),
    inference(resolution,[status(thm)],[c_341,c_1044])).

tff(c_1959,plain,(
    ! [B_62,A_63] : k3_xboole_0(k3_xboole_0(B_62,A_63),A_63) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_1824])).

tff(c_46,plain,(
    ! [B_44,A_43] : k5_relat_1(k6_relat_1(B_44),k6_relat_1(A_43)) = k6_relat_1(k3_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1001,plain,(
    ! [A_43,A_134,A_135] :
      ( k6_relat_1(k3_xboole_0(A_43,k3_xboole_0(A_134,A_135))) = k5_relat_1(k6_relat_1(A_134),k6_relat_1(A_43))
      | ~ r1_tarski(A_134,A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_46])).

tff(c_11622,plain,(
    ! [A_355,A_356,A_357] :
      ( k6_relat_1(k3_xboole_0(A_355,k3_xboole_0(A_356,A_357))) = k6_relat_1(k3_xboole_0(A_355,A_356))
      | ~ r1_tarski(A_356,A_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1001])).

tff(c_11785,plain,(
    ! [A_355,A_356,A_357] :
      ( k3_xboole_0(A_355,k3_xboole_0(A_356,A_357)) = k1_relat_1(k6_relat_1(k3_xboole_0(A_355,A_356)))
      | ~ r1_tarski(A_356,A_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11622,c_28])).

tff(c_32667,plain,(
    ! [A_601,A_602,A_603] :
      ( k3_xboole_0(A_601,k3_xboole_0(A_602,A_603)) = k3_xboole_0(A_601,A_602)
      | ~ r1_tarski(A_602,A_603) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_11785])).

tff(c_311,plain,(
    ! [A_83,B_84] : r1_tarski(k3_xboole_0(A_83,B_84),B_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_297])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_601,plain,(
    ! [A_107,B_108,A_109] :
      ( r1_tarski(A_107,B_108)
      | ~ r1_tarski(A_107,k3_xboole_0(A_109,B_108)) ) ),
    inference(resolution,[status(thm)],[c_330,c_8])).

tff(c_632,plain,(
    ! [A_83,A_109,B_108] : r1_tarski(k3_xboole_0(A_83,k3_xboole_0(A_109,B_108)),B_108) ),
    inference(resolution,[status(thm)],[c_311,c_601])).

tff(c_33639,plain,(
    ! [A_604,A_605,A_606] :
      ( r1_tarski(k3_xboole_0(A_604,A_605),A_606)
      | ~ r1_tarski(A_605,A_606) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32667,c_632])).

tff(c_34022,plain,(
    ! [A_611,B_612,A_613] :
      ( r1_tarski(k3_xboole_0(A_611,B_612),A_613)
      | ~ r1_tarski(A_611,A_613) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1959,c_33639])).

tff(c_34168,plain,(
    ! [B_35,A_34,A_613] :
      ( r1_tarski(k7_relat_1(B_35,A_34),A_613)
      | ~ r1_tarski(B_35,A_613)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_34022])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k7_relat_1(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_859,plain,(
    ! [B_126,C_127,A_128] :
      ( k10_relat_1(k5_relat_1(B_126,C_127),A_128) = k10_relat_1(B_126,k10_relat_1(C_127,A_128))
      | ~ v1_relat_1(C_127)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_875,plain,(
    ! [A_36,B_37,A_128] :
      ( k10_relat_1(k6_relat_1(A_36),k10_relat_1(B_37,A_128)) = k10_relat_1(k7_relat_1(B_37,A_36),A_128)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_859])).

tff(c_881,plain,(
    ! [A_36,B_37,A_128] :
      ( k10_relat_1(k6_relat_1(A_36),k10_relat_1(B_37,A_128)) = k10_relat_1(k7_relat_1(B_37,A_36),A_128)
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_875])).

tff(c_50,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1118,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1044])).

tff(c_1314,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_142])).

tff(c_30,plain,(
    ! [A_31] : k2_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_294,plain,(
    ! [A_83,B_84] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_83,B_84))) = k9_relat_1(k6_relat_1(A_83),B_84)
      | ~ v1_relat_1(k6_relat_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_22])).

tff(c_309,plain,(
    ! [A_83,B_84] : k9_relat_1(k6_relat_1(A_83),B_84) = k3_xboole_0(A_83,B_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_294])).

tff(c_637,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(A_110,k10_relat_1(B_111,k9_relat_1(B_111,A_110)))
      | ~ r1_tarski(A_110,k1_relat_1(B_111))
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_648,plain,(
    ! [B_84,A_83] :
      ( r1_tarski(B_84,k10_relat_1(k6_relat_1(A_83),k3_xboole_0(A_83,B_84)))
      | ~ r1_tarski(B_84,k1_relat_1(k6_relat_1(A_83)))
      | ~ v1_relat_1(k6_relat_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_637])).

tff(c_54704,plain,(
    ! [B_805,A_806] :
      ( r1_tarski(B_805,k10_relat_1(k6_relat_1(A_806),k3_xboole_0(A_806,B_805)))
      | ~ r1_tarski(B_805,A_806) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_648])).

tff(c_54880,plain,
    ( r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k6_relat_1('#skF_2'),k10_relat_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_54704])).

tff(c_54941,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k6_relat_1('#skF_2'),k10_relat_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54880])).

tff(c_55865,plain,
    ( r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_54941])).

tff(c_55885,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_55865])).

tff(c_1121,plain,(
    ! [B_138,A_139,C_140] :
      ( r1_tarski(k10_relat_1(B_138,A_139),k10_relat_1(C_140,A_139))
      | ~ r1_tarski(B_138,C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1144,plain,(
    ! [C_140,A_139,B_138] :
      ( k10_relat_1(C_140,A_139) = k10_relat_1(B_138,A_139)
      | ~ r1_tarski(k10_relat_1(C_140,A_139),k10_relat_1(B_138,A_139))
      | ~ r1_tarski(B_138,C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_1121,c_2])).

tff(c_55902,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_55885,c_1144])).

tff(c_55926,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_55902])).

tff(c_55927,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_55926])).

tff(c_55935,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_55927])).

tff(c_55950,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_55935])).

tff(c_55954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_55950])).

tff(c_55955,plain,(
    ~ r1_tarski(k7_relat_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_55927])).

tff(c_55959,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34168,c_55955])).

tff(c_55966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_55959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:46:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.29/11.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.29/11.72  
% 19.29/11.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.29/11.72  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 19.29/11.72  
% 19.29/11.72  %Foreground sorts:
% 19.29/11.72  
% 19.29/11.72  
% 19.29/11.72  %Background operators:
% 19.29/11.72  
% 19.29/11.72  
% 19.29/11.72  %Foreground operators:
% 19.29/11.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.29/11.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.29/11.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.29/11.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.29/11.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.29/11.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.29/11.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.29/11.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.29/11.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.29/11.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.29/11.72  tff('#skF_2', type, '#skF_2': $i).
% 19.29/11.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 19.29/11.72  tff('#skF_3', type, '#skF_3': $i).
% 19.29/11.72  tff('#skF_1', type, '#skF_1': $i).
% 19.29/11.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.29/11.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 19.29/11.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.29/11.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 19.29/11.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.29/11.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.29/11.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.29/11.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.29/11.72  
% 19.29/11.74  tff(f_115, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 19.29/11.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.29/11.74  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 19.29/11.74  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 19.29/11.74  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 19.29/11.74  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 19.29/11.74  tff(f_97, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 19.29/11.74  tff(f_105, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 19.29/11.74  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 19.29/11.74  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 19.29/11.74  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 19.29/11.74  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 19.29/11.74  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 19.29/11.74  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 19.29/11.74  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 19.29/11.74  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 19.29/11.74  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t179_relat_1)).
% 19.29/11.74  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 19.29/11.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.29/11.74  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.29/11.74  tff(c_121, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.29/11.74  tff(c_136, plain, (![B_62, A_63]: (k1_setfam_1(k2_tarski(B_62, A_63))=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_10, c_121])).
% 19.29/11.74  tff(c_18, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.29/11.74  tff(c_142, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_136, c_18])).
% 19.29/11.74  tff(c_34, plain, (![B_35, A_34]: (r1_tarski(k7_relat_1(B_35, A_34), B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.29/11.74  tff(c_28, plain, (![A_31]: (k1_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.29/11.74  tff(c_40, plain, (![A_40]: (v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.29/11.74  tff(c_268, plain, (![B_81, A_82]: (k5_relat_1(k6_relat_1(B_81), k6_relat_1(A_82))=k6_relat_1(k3_xboole_0(A_82, B_81)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.29/11.74  tff(c_36, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k7_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.29/11.74  tff(c_274, plain, (![A_82, B_81]: (k7_relat_1(k6_relat_1(A_82), B_81)=k6_relat_1(k3_xboole_0(A_82, B_81)) | ~v1_relat_1(k6_relat_1(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_268, c_36])).
% 19.29/11.74  tff(c_284, plain, (![A_82, B_81]: (k7_relat_1(k6_relat_1(A_82), B_81)=k6_relat_1(k3_xboole_0(A_82, B_81)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_274])).
% 19.29/11.74  tff(c_391, plain, (![B_94, A_95]: (k7_relat_1(B_94, A_95)=B_94 | ~r1_tarski(k1_relat_1(B_94), A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_93])).
% 19.29/11.74  tff(c_400, plain, (![A_31, A_95]: (k7_relat_1(k6_relat_1(A_31), A_95)=k6_relat_1(A_31) | ~r1_tarski(A_31, A_95) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_391])).
% 19.29/11.74  tff(c_977, plain, (![A_134, A_135]: (k6_relat_1(k3_xboole_0(A_134, A_135))=k6_relat_1(A_134) | ~r1_tarski(A_134, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_284, c_400])).
% 19.29/11.74  tff(c_1010, plain, (![A_134, A_135]: (k3_xboole_0(A_134, A_135)=k1_relat_1(k6_relat_1(A_134)) | ~r1_tarski(A_134, A_135))), inference(superposition, [status(thm), theory('equality')], [c_977, c_28])).
% 19.29/11.74  tff(c_1044, plain, (![A_136, A_137]: (k3_xboole_0(A_136, A_137)=A_136 | ~r1_tarski(A_136, A_137))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1010])).
% 19.29/11.74  tff(c_1092, plain, (![B_35, A_34]: (k3_xboole_0(k7_relat_1(B_35, A_34), B_35)=k7_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_34, c_1044])).
% 19.29/11.74  tff(c_1117, plain, (![B_35, A_34]: (k3_xboole_0(B_35, k7_relat_1(B_35, A_34))=k7_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1092])).
% 19.29/11.74  tff(c_288, plain, (![A_83, B_84]: (k7_relat_1(k6_relat_1(A_83), B_84)=k6_relat_1(k3_xboole_0(A_83, B_84)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_274])).
% 19.29/11.74  tff(c_32, plain, (![B_33, A_32]: (r1_tarski(k1_relat_1(k7_relat_1(B_33, A_32)), A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.29/11.74  tff(c_297, plain, (![A_83, B_84]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_83, B_84))), B_84) | ~v1_relat_1(k6_relat_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_288, c_32])).
% 19.29/11.74  tff(c_330, plain, (![A_86, B_87]: (r1_tarski(k3_xboole_0(A_86, B_87), B_87))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_297])).
% 19.29/11.74  tff(c_341, plain, (![B_62, A_63]: (r1_tarski(k3_xboole_0(B_62, A_63), B_62))), inference(superposition, [status(thm), theory('equality')], [c_142, c_330])).
% 19.29/11.74  tff(c_1824, plain, (![B_152, A_153]: (k3_xboole_0(k3_xboole_0(B_152, A_153), B_152)=k3_xboole_0(B_152, A_153))), inference(resolution, [status(thm)], [c_341, c_1044])).
% 19.29/11.74  tff(c_1959, plain, (![B_62, A_63]: (k3_xboole_0(k3_xboole_0(B_62, A_63), A_63)=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_142, c_1824])).
% 19.29/11.74  tff(c_46, plain, (![B_44, A_43]: (k5_relat_1(k6_relat_1(B_44), k6_relat_1(A_43))=k6_relat_1(k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.29/11.74  tff(c_1001, plain, (![A_43, A_134, A_135]: (k6_relat_1(k3_xboole_0(A_43, k3_xboole_0(A_134, A_135)))=k5_relat_1(k6_relat_1(A_134), k6_relat_1(A_43)) | ~r1_tarski(A_134, A_135))), inference(superposition, [status(thm), theory('equality')], [c_977, c_46])).
% 19.29/11.74  tff(c_11622, plain, (![A_355, A_356, A_357]: (k6_relat_1(k3_xboole_0(A_355, k3_xboole_0(A_356, A_357)))=k6_relat_1(k3_xboole_0(A_355, A_356)) | ~r1_tarski(A_356, A_357))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1001])).
% 19.29/11.74  tff(c_11785, plain, (![A_355, A_356, A_357]: (k3_xboole_0(A_355, k3_xboole_0(A_356, A_357))=k1_relat_1(k6_relat_1(k3_xboole_0(A_355, A_356))) | ~r1_tarski(A_356, A_357))), inference(superposition, [status(thm), theory('equality')], [c_11622, c_28])).
% 19.29/11.74  tff(c_32667, plain, (![A_601, A_602, A_603]: (k3_xboole_0(A_601, k3_xboole_0(A_602, A_603))=k3_xboole_0(A_601, A_602) | ~r1_tarski(A_602, A_603))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_11785])).
% 19.29/11.74  tff(c_311, plain, (![A_83, B_84]: (r1_tarski(k3_xboole_0(A_83, B_84), B_84))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_297])).
% 19.29/11.74  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.29/11.74  tff(c_601, plain, (![A_107, B_108, A_109]: (r1_tarski(A_107, B_108) | ~r1_tarski(A_107, k3_xboole_0(A_109, B_108)))), inference(resolution, [status(thm)], [c_330, c_8])).
% 19.29/11.74  tff(c_632, plain, (![A_83, A_109, B_108]: (r1_tarski(k3_xboole_0(A_83, k3_xboole_0(A_109, B_108)), B_108))), inference(resolution, [status(thm)], [c_311, c_601])).
% 19.29/11.74  tff(c_33639, plain, (![A_604, A_605, A_606]: (r1_tarski(k3_xboole_0(A_604, A_605), A_606) | ~r1_tarski(A_605, A_606))), inference(superposition, [status(thm), theory('equality')], [c_32667, c_632])).
% 19.29/11.74  tff(c_34022, plain, (![A_611, B_612, A_613]: (r1_tarski(k3_xboole_0(A_611, B_612), A_613) | ~r1_tarski(A_611, A_613))), inference(superposition, [status(thm), theory('equality')], [c_1959, c_33639])).
% 19.29/11.74  tff(c_34168, plain, (![B_35, A_34, A_613]: (r1_tarski(k7_relat_1(B_35, A_34), A_613) | ~r1_tarski(B_35, A_613) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_1117, c_34022])).
% 19.29/11.74  tff(c_20, plain, (![A_19, B_20]: (v1_relat_1(k7_relat_1(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.29/11.74  tff(c_48, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 19.29/11.74  tff(c_859, plain, (![B_126, C_127, A_128]: (k10_relat_1(k5_relat_1(B_126, C_127), A_128)=k10_relat_1(B_126, k10_relat_1(C_127, A_128)) | ~v1_relat_1(C_127) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_71])).
% 19.29/11.74  tff(c_875, plain, (![A_36, B_37, A_128]: (k10_relat_1(k6_relat_1(A_36), k10_relat_1(B_37, A_128))=k10_relat_1(k7_relat_1(B_37, A_36), A_128) | ~v1_relat_1(B_37) | ~v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_36, c_859])).
% 19.29/11.74  tff(c_881, plain, (![A_36, B_37, A_128]: (k10_relat_1(k6_relat_1(A_36), k10_relat_1(B_37, A_128))=k10_relat_1(k7_relat_1(B_37, A_36), A_128) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_875])).
% 19.29/11.74  tff(c_50, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 19.29/11.74  tff(c_1118, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1044])).
% 19.29/11.74  tff(c_1314, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1118, c_142])).
% 19.29/11.74  tff(c_30, plain, (![A_31]: (k2_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.29/11.74  tff(c_22, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.29/11.74  tff(c_294, plain, (![A_83, B_84]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_83, B_84)))=k9_relat_1(k6_relat_1(A_83), B_84) | ~v1_relat_1(k6_relat_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_288, c_22])).
% 19.29/11.74  tff(c_309, plain, (![A_83, B_84]: (k9_relat_1(k6_relat_1(A_83), B_84)=k3_xboole_0(A_83, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_294])).
% 19.29/11.74  tff(c_637, plain, (![A_110, B_111]: (r1_tarski(A_110, k10_relat_1(B_111, k9_relat_1(B_111, A_110))) | ~r1_tarski(A_110, k1_relat_1(B_111)) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_103])).
% 19.29/11.74  tff(c_648, plain, (![B_84, A_83]: (r1_tarski(B_84, k10_relat_1(k6_relat_1(A_83), k3_xboole_0(A_83, B_84))) | ~r1_tarski(B_84, k1_relat_1(k6_relat_1(A_83))) | ~v1_relat_1(k6_relat_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_309, c_637])).
% 19.29/11.74  tff(c_54704, plain, (![B_805, A_806]: (r1_tarski(B_805, k10_relat_1(k6_relat_1(A_806), k3_xboole_0(A_806, B_805))) | ~r1_tarski(B_805, A_806))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_648])).
% 19.29/11.74  tff(c_54880, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k6_relat_1('#skF_2'), k10_relat_1('#skF_1', '#skF_3'))) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1314, c_54704])).
% 19.29/11.74  tff(c_54941, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k6_relat_1('#skF_2'), k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54880])).
% 19.29/11.74  tff(c_55865, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_881, c_54941])).
% 19.29/11.74  tff(c_55885, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_55865])).
% 19.29/11.74  tff(c_1121, plain, (![B_138, A_139, C_140]: (r1_tarski(k10_relat_1(B_138, A_139), k10_relat_1(C_140, A_139)) | ~r1_tarski(B_138, C_140) | ~v1_relat_1(C_140) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_64])).
% 19.29/11.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.29/11.74  tff(c_1144, plain, (![C_140, A_139, B_138]: (k10_relat_1(C_140, A_139)=k10_relat_1(B_138, A_139) | ~r1_tarski(k10_relat_1(C_140, A_139), k10_relat_1(B_138, A_139)) | ~r1_tarski(B_138, C_140) | ~v1_relat_1(C_140) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_1121, c_2])).
% 19.29/11.74  tff(c_55902, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k7_relat_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_55885, c_1144])).
% 19.29/11.74  tff(c_55926, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k7_relat_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_55902])).
% 19.29/11.74  tff(c_55927, plain, (~r1_tarski(k7_relat_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_55926])).
% 19.29/11.74  tff(c_55935, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_55927])).
% 19.29/11.74  tff(c_55950, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_55935])).
% 19.29/11.74  tff(c_55954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_55950])).
% 19.29/11.74  tff(c_55955, plain, (~r1_tarski(k7_relat_1('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_55927])).
% 19.29/11.74  tff(c_55959, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34168, c_55955])).
% 19.29/11.74  tff(c_55966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_55959])).
% 19.29/11.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.29/11.74  
% 19.29/11.74  Inference rules
% 19.29/11.74  ----------------------
% 19.29/11.74  #Ref     : 0
% 19.29/11.74  #Sup     : 14246
% 19.29/11.74  #Fact    : 0
% 19.29/11.74  #Define  : 0
% 19.29/11.74  #Split   : 4
% 19.29/11.74  #Chain   : 0
% 19.29/11.74  #Close   : 0
% 19.29/11.74  
% 19.29/11.74  Ordering : KBO
% 19.29/11.74  
% 19.29/11.74  Simplification rules
% 19.29/11.74  ----------------------
% 19.29/11.74  #Subsume      : 2109
% 19.29/11.74  #Demod        : 7913
% 19.29/11.74  #Tautology    : 4286
% 19.29/11.74  #SimpNegUnit  : 4
% 19.29/11.74  #BackRed      : 0
% 19.29/11.74  
% 19.29/11.74  #Partial instantiations: 0
% 19.29/11.74  #Strategies tried      : 1
% 19.29/11.74  
% 19.29/11.74  Timing (in seconds)
% 19.29/11.74  ----------------------
% 19.29/11.74  Preprocessing        : 0.53
% 19.29/11.74  Parsing              : 0.27
% 19.29/11.74  CNF conversion       : 0.04
% 19.29/11.74  Main loop            : 10.38
% 19.29/11.74  Inferencing          : 1.33
% 19.29/11.74  Reduction            : 5.46
% 19.29/11.74  Demodulation         : 4.95
% 19.29/11.74  BG Simplification    : 0.20
% 19.29/11.74  Subsumption          : 2.92
% 19.29/11.74  Abstraction          : 0.30
% 19.29/11.74  MUC search           : 0.00
% 19.29/11.74  Cooper               : 0.00
% 19.29/11.74  Total                : 10.95
% 19.29/11.74  Index Insertion      : 0.00
% 19.29/11.74  Index Deletion       : 0.00
% 19.29/11.74  Index Matching       : 0.00
% 19.29/11.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
