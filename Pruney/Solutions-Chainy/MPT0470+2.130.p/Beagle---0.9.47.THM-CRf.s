%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:19 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 154 expanded)
%              Number of leaves         :   43 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 208 expanded)
%              Number of equality atoms :   52 (  98 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_101,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_52,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_99,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_1'(A_44),A_44)
      | v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [A_86,C_87,B_88] :
      ( ~ r2_hidden(A_86,C_87)
      | ~ r1_xboole_0(k2_tarski(A_86,B_88),C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_141,plain,(
    ! [A_89] : ~ r2_hidden(A_89,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_146,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_141])).

tff(c_40,plain,(
    ! [A_62,B_63] :
      ( v1_relat_1(k5_relat_1(A_62,B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_134,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_131])).

tff(c_266,plain,(
    ! [A_106,C_107,B_108] : k4_xboole_0(k2_zfmisc_1(A_106,C_107),k2_zfmisc_1(B_108,C_107)) = k2_zfmisc_1(k4_xboole_0(A_106,B_108),C_107) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_277,plain,(
    ! [B_108,C_107] : k2_zfmisc_1(k4_xboole_0(B_108,B_108),C_107) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_134])).

tff(c_291,plain,(
    ! [C_107] : k2_zfmisc_1(k1_xboole_0,C_107) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_277])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_796,plain,(
    ! [A_144,B_145] :
      ( k1_relat_1(k5_relat_1(A_144,B_145)) = k1_relat_1(A_144)
      | ~ r1_tarski(k2_relat_1(A_144),k1_relat_1(B_145))
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_805,plain,(
    ! [B_145] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_145)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_145))
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_796])).

tff(c_812,plain,(
    ! [B_146] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_146)) = k1_xboole_0
      | ~ v1_relat_1(B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_8,c_50,c_805])).

tff(c_42,plain,(
    ! [A_64] :
      ( k3_xboole_0(A_64,k2_zfmisc_1(k1_relat_1(A_64),k2_relat_1(A_64))) = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_830,plain,(
    ! [B_146] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_146),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_146)))) = k5_relat_1(k1_xboole_0,B_146)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_146))
      | ~ v1_relat_1(B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_42])).

tff(c_847,plain,(
    ! [B_147] :
      ( k5_relat_1(k1_xboole_0,B_147) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_147))
      | ~ v1_relat_1(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_291,c_830])).

tff(c_854,plain,(
    ! [B_63] :
      ( k5_relat_1(k1_xboole_0,B_63) = k1_xboole_0
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_847])).

tff(c_860,plain,(
    ! [B_148] :
      ( k5_relat_1(k1_xboole_0,B_148) = k1_xboole_0
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_854])).

tff(c_869,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_860])).

tff(c_876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_869])).

tff(c_877,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_950,plain,(
    ! [A_162,C_163,B_164] :
      ( ~ r2_hidden(A_162,C_163)
      | ~ r1_xboole_0(k2_tarski(A_162,B_164),C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_965,plain,(
    ! [A_168] : ~ r2_hidden(A_168,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_950])).

tff(c_970,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_965])).

tff(c_902,plain,(
    ! [A_156,B_157] : k5_xboole_0(A_156,k3_xboole_0(A_156,B_157)) = k4_xboole_0(A_156,B_157) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_914,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_902])).

tff(c_917,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_914])).

tff(c_1035,plain,(
    ! [C_175,A_176,B_177] : k4_xboole_0(k2_zfmisc_1(C_175,A_176),k2_zfmisc_1(C_175,B_177)) = k2_zfmisc_1(C_175,k4_xboole_0(A_176,B_177)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1042,plain,(
    ! [C_175,B_177] : k2_zfmisc_1(C_175,k4_xboole_0(B_177,B_177)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_917])).

tff(c_1051,plain,(
    ! [C_175] : k2_zfmisc_1(C_175,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_1042])).

tff(c_1617,plain,(
    ! [B_217,A_218] :
      ( k2_relat_1(k5_relat_1(B_217,A_218)) = k2_relat_1(A_218)
      | ~ r1_tarski(k1_relat_1(A_218),k2_relat_1(B_217))
      | ~ v1_relat_1(B_217)
      | ~ v1_relat_1(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1620,plain,(
    ! [B_217] :
      ( k2_relat_1(k5_relat_1(B_217,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_217))
      | ~ v1_relat_1(B_217)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1617])).

tff(c_1628,plain,(
    ! [B_219] :
      ( k2_relat_1(k5_relat_1(B_219,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_8,c_48,c_1620])).

tff(c_1640,plain,(
    ! [B_219] :
      ( k3_xboole_0(k5_relat_1(B_219,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_219,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_219,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_219,k1_xboole_0))
      | ~ v1_relat_1(B_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1628,c_42])).

tff(c_1648,plain,(
    ! [B_220] :
      ( k5_relat_1(B_220,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_220,k1_xboole_0))
      | ~ v1_relat_1(B_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1051,c_1640])).

tff(c_1652,plain,(
    ! [A_62] :
      ( k5_relat_1(A_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_40,c_1648])).

tff(c_1656,plain,(
    ! [A_221] :
      ( k5_relat_1(A_221,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_221) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_1652])).

tff(c_1665,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_1656])).

tff(c_1671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_877,c_1665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.48/1.53  
% 3.48/1.53  %Foreground sorts:
% 3.48/1.53  
% 3.48/1.53  
% 3.48/1.53  %Background operators:
% 3.48/1.53  
% 3.48/1.53  
% 3.48/1.53  %Foreground operators:
% 3.48/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.48/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.48/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.48/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.48/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.48/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.48/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.48/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.48/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.48/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.48/1.53  
% 3.48/1.55  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.48/1.55  tff(f_70, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.48/1.55  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.48/1.55  tff(f_58, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.48/1.55  tff(f_76, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.48/1.55  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.48/1.55  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.48/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.48/1.55  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.48/1.55  tff(f_53, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 3.48/1.55  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.48/1.55  tff(f_101, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.48/1.55  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.48/1.55  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.48/1.55  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.48/1.55  tff(c_52, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.48/1.55  tff(c_99, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.48/1.55  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.48/1.55  tff(c_38, plain, (![A_44]: (r2_hidden('#skF_1'(A_44), A_44) | v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.55  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.55  tff(c_135, plain, (![A_86, C_87, B_88]: (~r2_hidden(A_86, C_87) | ~r1_xboole_0(k2_tarski(A_86, B_88), C_87))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.55  tff(c_141, plain, (![A_89]: (~r2_hidden(A_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_135])).
% 3.48/1.55  tff(c_146, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_141])).
% 3.48/1.55  tff(c_40, plain, (![A_62, B_63]: (v1_relat_1(k5_relat_1(A_62, B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.48/1.55  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.55  tff(c_12, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.55  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.55  tff(c_119, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.55  tff(c_131, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 3.48/1.55  tff(c_134, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_131])).
% 3.48/1.55  tff(c_266, plain, (![A_106, C_107, B_108]: (k4_xboole_0(k2_zfmisc_1(A_106, C_107), k2_zfmisc_1(B_108, C_107))=k2_zfmisc_1(k4_xboole_0(A_106, B_108), C_107))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.48/1.55  tff(c_277, plain, (![B_108, C_107]: (k2_zfmisc_1(k4_xboole_0(B_108, B_108), C_107)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_266, c_134])).
% 3.48/1.55  tff(c_291, plain, (![C_107]: (k2_zfmisc_1(k1_xboole_0, C_107)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_277])).
% 3.48/1.55  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.55  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.48/1.55  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.48/1.55  tff(c_796, plain, (![A_144, B_145]: (k1_relat_1(k5_relat_1(A_144, B_145))=k1_relat_1(A_144) | ~r1_tarski(k2_relat_1(A_144), k1_relat_1(B_145)) | ~v1_relat_1(B_145) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.48/1.55  tff(c_805, plain, (![B_145]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_145))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_145)) | ~v1_relat_1(B_145) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_796])).
% 3.48/1.55  tff(c_812, plain, (![B_146]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_146))=k1_xboole_0 | ~v1_relat_1(B_146))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_8, c_50, c_805])).
% 3.48/1.55  tff(c_42, plain, (![A_64]: (k3_xboole_0(A_64, k2_zfmisc_1(k1_relat_1(A_64), k2_relat_1(A_64)))=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.55  tff(c_830, plain, (![B_146]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_146), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_146))))=k5_relat_1(k1_xboole_0, B_146) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_146)) | ~v1_relat_1(B_146))), inference(superposition, [status(thm), theory('equality')], [c_812, c_42])).
% 3.48/1.55  tff(c_847, plain, (![B_147]: (k5_relat_1(k1_xboole_0, B_147)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_147)) | ~v1_relat_1(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_291, c_830])).
% 3.48/1.55  tff(c_854, plain, (![B_63]: (k5_relat_1(k1_xboole_0, B_63)=k1_xboole_0 | ~v1_relat_1(B_63) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_847])).
% 3.48/1.55  tff(c_860, plain, (![B_148]: (k5_relat_1(k1_xboole_0, B_148)=k1_xboole_0 | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_854])).
% 3.48/1.55  tff(c_869, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_860])).
% 3.48/1.55  tff(c_876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_869])).
% 3.48/1.55  tff(c_877, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.48/1.55  tff(c_950, plain, (![A_162, C_163, B_164]: (~r2_hidden(A_162, C_163) | ~r1_xboole_0(k2_tarski(A_162, B_164), C_163))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.55  tff(c_965, plain, (![A_168]: (~r2_hidden(A_168, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_950])).
% 3.48/1.55  tff(c_970, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_965])).
% 3.48/1.55  tff(c_902, plain, (![A_156, B_157]: (k5_xboole_0(A_156, k3_xboole_0(A_156, B_157))=k4_xboole_0(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.55  tff(c_914, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_902])).
% 3.48/1.55  tff(c_917, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_914])).
% 3.48/1.55  tff(c_1035, plain, (![C_175, A_176, B_177]: (k4_xboole_0(k2_zfmisc_1(C_175, A_176), k2_zfmisc_1(C_175, B_177))=k2_zfmisc_1(C_175, k4_xboole_0(A_176, B_177)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.48/1.55  tff(c_1042, plain, (![C_175, B_177]: (k2_zfmisc_1(C_175, k4_xboole_0(B_177, B_177))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1035, c_917])).
% 3.48/1.55  tff(c_1051, plain, (![C_175]: (k2_zfmisc_1(C_175, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_917, c_1042])).
% 3.48/1.55  tff(c_1617, plain, (![B_217, A_218]: (k2_relat_1(k5_relat_1(B_217, A_218))=k2_relat_1(A_218) | ~r1_tarski(k1_relat_1(A_218), k2_relat_1(B_217)) | ~v1_relat_1(B_217) | ~v1_relat_1(A_218))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.48/1.55  tff(c_1620, plain, (![B_217]: (k2_relat_1(k5_relat_1(B_217, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_217)) | ~v1_relat_1(B_217) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1617])).
% 3.48/1.55  tff(c_1628, plain, (![B_219]: (k2_relat_1(k5_relat_1(B_219, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_219))), inference(demodulation, [status(thm), theory('equality')], [c_970, c_8, c_48, c_1620])).
% 3.48/1.55  tff(c_1640, plain, (![B_219]: (k3_xboole_0(k5_relat_1(B_219, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_219, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_219, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_219, k1_xboole_0)) | ~v1_relat_1(B_219))), inference(superposition, [status(thm), theory('equality')], [c_1628, c_42])).
% 3.48/1.55  tff(c_1648, plain, (![B_220]: (k5_relat_1(B_220, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_220, k1_xboole_0)) | ~v1_relat_1(B_220))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1051, c_1640])).
% 3.48/1.55  tff(c_1652, plain, (![A_62]: (k5_relat_1(A_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_40, c_1648])).
% 3.48/1.55  tff(c_1656, plain, (![A_221]: (k5_relat_1(A_221, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_221))), inference(demodulation, [status(thm), theory('equality')], [c_970, c_1652])).
% 3.48/1.55  tff(c_1665, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_1656])).
% 3.48/1.55  tff(c_1671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_877, c_1665])).
% 3.48/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.55  
% 3.48/1.55  Inference rules
% 3.48/1.55  ----------------------
% 3.48/1.55  #Ref     : 2
% 3.48/1.55  #Sup     : 363
% 3.48/1.55  #Fact    : 0
% 3.48/1.55  #Define  : 0
% 3.48/1.55  #Split   : 1
% 3.48/1.55  #Chain   : 0
% 3.48/1.55  #Close   : 0
% 3.48/1.55  
% 3.48/1.55  Ordering : KBO
% 3.48/1.55  
% 3.48/1.55  Simplification rules
% 3.48/1.55  ----------------------
% 3.48/1.55  #Subsume      : 4
% 3.48/1.55  #Demod        : 453
% 3.48/1.55  #Tautology    : 251
% 3.48/1.55  #SimpNegUnit  : 2
% 3.48/1.55  #BackRed      : 4
% 3.48/1.55  
% 3.48/1.55  #Partial instantiations: 0
% 3.48/1.55  #Strategies tried      : 1
% 3.48/1.55  
% 3.48/1.55  Timing (in seconds)
% 3.48/1.55  ----------------------
% 3.48/1.55  Preprocessing        : 0.33
% 3.48/1.55  Parsing              : 0.17
% 3.48/1.55  CNF conversion       : 0.02
% 3.48/1.55  Main loop            : 0.45
% 3.48/1.55  Inferencing          : 0.17
% 3.48/1.55  Reduction            : 0.17
% 3.48/1.55  Demodulation         : 0.13
% 3.48/1.55  BG Simplification    : 0.02
% 3.48/1.55  Subsumption          : 0.06
% 3.48/1.55  Abstraction          : 0.03
% 3.48/1.55  MUC search           : 0.00
% 3.48/1.55  Cooper               : 0.00
% 3.48/1.55  Total                : 0.81
% 3.48/1.55  Index Insertion      : 0.00
% 3.48/1.55  Index Deletion       : 0.00
% 3.48/1.55  Index Matching       : 0.00
% 3.48/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
