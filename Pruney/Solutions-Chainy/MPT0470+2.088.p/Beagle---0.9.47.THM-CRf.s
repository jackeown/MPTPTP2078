%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:13 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 163 expanded)
%              Number of leaves         :   40 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 208 expanded)
%              Number of equality atoms :   57 ( 118 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_93,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_93,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    ! [A_56] :
      ( v1_relat_1(A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_38,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_146,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_137])).

tff(c_155,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_152,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_137])).

tff(c_186,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_152])).

tff(c_249,plain,(
    ! [A_84,C_85,B_86] : k4_xboole_0(k2_zfmisc_1(A_84,C_85),k2_zfmisc_1(B_86,C_85)) = k2_zfmisc_1(k4_xboole_0(A_84,B_86),C_85) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_256,plain,(
    ! [B_86,C_85] : k2_zfmisc_1(k4_xboole_0(B_86,B_86),C_85) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_186])).

tff(c_265,plain,(
    ! [C_85] : k2_zfmisc_1(k1_xboole_0,C_85) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_256])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_818,plain,(
    ! [A_127,B_128] :
      ( k1_relat_1(k5_relat_1(A_127,B_128)) = k1_relat_1(A_127)
      | ~ r1_tarski(k2_relat_1(A_127),k1_relat_1(B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_827,plain,(
    ! [B_128] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_128)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_818])).

tff(c_834,plain,(
    ! [B_129] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_129)) = k1_xboole_0
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_12,c_48,c_827])).

tff(c_40,plain,(
    ! [A_48] :
      ( k3_xboole_0(A_48,k2_zfmisc_1(k1_relat_1(A_48),k2_relat_1(A_48))) = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_849,plain,(
    ! [B_129] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_129),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_129)))) = k5_relat_1(k1_xboole_0,B_129)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_129))
      | ~ v1_relat_1(B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_40])).

tff(c_864,plain,(
    ! [B_130] :
      ( k5_relat_1(k1_xboole_0,B_130) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_130))
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_265,c_849])).

tff(c_871,plain,(
    ! [B_47] :
      ( k5_relat_1(k1_xboole_0,B_47) = k1_xboole_0
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_864])).

tff(c_877,plain,(
    ! [B_131] :
      ( k5_relat_1(k1_xboole_0,B_131) = k1_xboole_0
      | ~ v1_relat_1(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_871])).

tff(c_886,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_877])).

tff(c_893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_886])).

tff(c_894,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_943,plain,(
    ! [A_142,B_143] : k5_xboole_0(A_142,k3_xboole_0(A_142,B_143)) = k4_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_952,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_943])).

tff(c_961,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_952])).

tff(c_958,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_943])).

tff(c_997,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_958])).

tff(c_1060,plain,(
    ! [C_157,A_158,B_159] : k4_xboole_0(k2_zfmisc_1(C_157,A_158),k2_zfmisc_1(C_157,B_159)) = k2_zfmisc_1(C_157,k4_xboole_0(A_158,B_159)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1067,plain,(
    ! [C_157,B_159] : k2_zfmisc_1(C_157,k4_xboole_0(B_159,B_159)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_997])).

tff(c_1076,plain,(
    ! [C_157] : k2_zfmisc_1(C_157,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_1067])).

tff(c_1669,plain,(
    ! [B_199,A_200] :
      ( k2_relat_1(k5_relat_1(B_199,A_200)) = k2_relat_1(A_200)
      | ~ r1_tarski(k1_relat_1(A_200),k2_relat_1(B_199))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1672,plain,(
    ! [B_199] :
      ( k2_relat_1(k5_relat_1(B_199,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_199))
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1669])).

tff(c_1680,plain,(
    ! [B_201] :
      ( k2_relat_1(k5_relat_1(B_201,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_12,c_46,c_1672])).

tff(c_1692,plain,(
    ! [B_201] :
      ( k3_xboole_0(k5_relat_1(B_201,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_201,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_201,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_201,k1_xboole_0))
      | ~ v1_relat_1(B_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_40])).

tff(c_1700,plain,(
    ! [B_202] :
      ( k5_relat_1(B_202,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_202,k1_xboole_0))
      | ~ v1_relat_1(B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1076,c_1692])).

tff(c_1704,plain,(
    ! [A_46] :
      ( k5_relat_1(A_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_38,c_1700])).

tff(c_1708,plain,(
    ! [A_203] :
      ( k5_relat_1(A_203,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1704])).

tff(c_1717,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1708])).

tff(c_1723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_894,c_1717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.60  
% 3.24/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.60  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.24/1.60  
% 3.24/1.60  %Foreground sorts:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Background operators:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Foreground operators:
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.24/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.24/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.24/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.24/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.24/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.24/1.60  
% 3.59/1.62  tff(f_100, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.59/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.59/1.62  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.59/1.62  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.59/1.62  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.59/1.62  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.59/1.62  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.59/1.62  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.59/1.62  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.59/1.62  tff(f_56, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 3.59/1.62  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.59/1.62  tff(f_93, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.59/1.62  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.59/1.62  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.59/1.62  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.59/1.62  tff(c_50, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.59/1.62  tff(c_93, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.59/1.62  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.59/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.59/1.62  tff(c_62, plain, (![A_56]: (v1_relat_1(A_56) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.59/1.62  tff(c_66, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_62])).
% 3.59/1.62  tff(c_38, plain, (![A_46, B_47]: (v1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.59/1.62  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.59/1.62  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.59/1.62  tff(c_8, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.62  tff(c_137, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.59/1.62  tff(c_146, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_137])).
% 3.59/1.62  tff(c_155, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_146])).
% 3.59/1.62  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.59/1.62  tff(c_152, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_137])).
% 3.59/1.62  tff(c_186, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_152])).
% 3.59/1.62  tff(c_249, plain, (![A_84, C_85, B_86]: (k4_xboole_0(k2_zfmisc_1(A_84, C_85), k2_zfmisc_1(B_86, C_85))=k2_zfmisc_1(k4_xboole_0(A_84, B_86), C_85))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.59/1.62  tff(c_256, plain, (![B_86, C_85]: (k2_zfmisc_1(k4_xboole_0(B_86, B_86), C_85)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_249, c_186])).
% 3.59/1.62  tff(c_265, plain, (![C_85]: (k2_zfmisc_1(k1_xboole_0, C_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_256])).
% 3.59/1.62  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.59/1.62  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.59/1.62  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.59/1.62  tff(c_818, plain, (![A_127, B_128]: (k1_relat_1(k5_relat_1(A_127, B_128))=k1_relat_1(A_127) | ~r1_tarski(k2_relat_1(A_127), k1_relat_1(B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.59/1.62  tff(c_827, plain, (![B_128]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_128))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_818])).
% 3.59/1.62  tff(c_834, plain, (![B_129]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_129))=k1_xboole_0 | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_12, c_48, c_827])).
% 3.59/1.62  tff(c_40, plain, (![A_48]: (k3_xboole_0(A_48, k2_zfmisc_1(k1_relat_1(A_48), k2_relat_1(A_48)))=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.59/1.62  tff(c_849, plain, (![B_129]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_129), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_129))))=k5_relat_1(k1_xboole_0, B_129) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_129)) | ~v1_relat_1(B_129))), inference(superposition, [status(thm), theory('equality')], [c_834, c_40])).
% 3.59/1.62  tff(c_864, plain, (![B_130]: (k5_relat_1(k1_xboole_0, B_130)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_130)) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_265, c_849])).
% 3.59/1.62  tff(c_871, plain, (![B_47]: (k5_relat_1(k1_xboole_0, B_47)=k1_xboole_0 | ~v1_relat_1(B_47) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_864])).
% 3.59/1.62  tff(c_877, plain, (![B_131]: (k5_relat_1(k1_xboole_0, B_131)=k1_xboole_0 | ~v1_relat_1(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_871])).
% 3.59/1.62  tff(c_886, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_877])).
% 3.59/1.62  tff(c_893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_886])).
% 3.59/1.62  tff(c_894, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.59/1.62  tff(c_943, plain, (![A_142, B_143]: (k5_xboole_0(A_142, k3_xboole_0(A_142, B_143))=k4_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.59/1.62  tff(c_952, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_943])).
% 3.59/1.62  tff(c_961, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_952])).
% 3.59/1.62  tff(c_958, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_943])).
% 3.59/1.62  tff(c_997, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_961, c_958])).
% 3.59/1.62  tff(c_1060, plain, (![C_157, A_158, B_159]: (k4_xboole_0(k2_zfmisc_1(C_157, A_158), k2_zfmisc_1(C_157, B_159))=k2_zfmisc_1(C_157, k4_xboole_0(A_158, B_159)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.59/1.62  tff(c_1067, plain, (![C_157, B_159]: (k2_zfmisc_1(C_157, k4_xboole_0(B_159, B_159))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1060, c_997])).
% 3.59/1.62  tff(c_1076, plain, (![C_157]: (k2_zfmisc_1(C_157, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_997, c_1067])).
% 3.59/1.62  tff(c_1669, plain, (![B_199, A_200]: (k2_relat_1(k5_relat_1(B_199, A_200))=k2_relat_1(A_200) | ~r1_tarski(k1_relat_1(A_200), k2_relat_1(B_199)) | ~v1_relat_1(B_199) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.59/1.62  tff(c_1672, plain, (![B_199]: (k2_relat_1(k5_relat_1(B_199, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_199)) | ~v1_relat_1(B_199) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1669])).
% 3.59/1.62  tff(c_1680, plain, (![B_201]: (k2_relat_1(k5_relat_1(B_201, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_201))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_12, c_46, c_1672])).
% 3.59/1.62  tff(c_1692, plain, (![B_201]: (k3_xboole_0(k5_relat_1(B_201, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_201, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_201, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_201, k1_xboole_0)) | ~v1_relat_1(B_201))), inference(superposition, [status(thm), theory('equality')], [c_1680, c_40])).
% 3.59/1.62  tff(c_1700, plain, (![B_202]: (k5_relat_1(B_202, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_202, k1_xboole_0)) | ~v1_relat_1(B_202))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1076, c_1692])).
% 3.59/1.62  tff(c_1704, plain, (![A_46]: (k5_relat_1(A_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_38, c_1700])).
% 3.59/1.62  tff(c_1708, plain, (![A_203]: (k5_relat_1(A_203, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_203))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1704])).
% 3.59/1.62  tff(c_1717, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_1708])).
% 3.59/1.62  tff(c_1723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_894, c_1717])).
% 3.59/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.62  
% 3.59/1.62  Inference rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Ref     : 0
% 3.59/1.62  #Sup     : 394
% 3.59/1.62  #Fact    : 0
% 3.59/1.62  #Define  : 0
% 3.59/1.62  #Split   : 1
% 3.59/1.62  #Chain   : 0
% 3.59/1.62  #Close   : 0
% 3.59/1.62  
% 3.59/1.62  Ordering : KBO
% 3.59/1.62  
% 3.59/1.62  Simplification rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Subsume      : 3
% 3.59/1.62  #Demod        : 436
% 3.59/1.62  #Tautology    : 275
% 3.59/1.62  #SimpNegUnit  : 2
% 3.59/1.62  #BackRed      : 6
% 3.59/1.62  
% 3.59/1.62  #Partial instantiations: 0
% 3.59/1.62  #Strategies tried      : 1
% 3.59/1.62  
% 3.59/1.62  Timing (in seconds)
% 3.59/1.62  ----------------------
% 3.59/1.62  Preprocessing        : 0.35
% 3.59/1.62  Parsing              : 0.20
% 3.59/1.62  CNF conversion       : 0.02
% 3.59/1.62  Main loop            : 0.47
% 3.59/1.62  Inferencing          : 0.17
% 3.59/1.62  Reduction            : 0.17
% 3.59/1.62  Demodulation         : 0.13
% 3.59/1.62  BG Simplification    : 0.03
% 3.59/1.62  Subsumption          : 0.06
% 3.59/1.62  Abstraction          : 0.03
% 3.59/1.62  MUC search           : 0.00
% 3.59/1.62  Cooper               : 0.00
% 3.59/1.62  Total                : 0.85
% 3.59/1.62  Index Insertion      : 0.00
% 3.59/1.62  Index Deletion       : 0.00
% 3.59/1.62  Index Matching       : 0.00
% 3.59/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
