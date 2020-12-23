%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0752+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:48 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   48 (  99 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 136 expanded)
%              Number of equality atoms :    6 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_43,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_12,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_28])).

tff(c_23,plain,(
    ! [A_11] :
      ( v1_relat_1(A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_33,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_27])).

tff(c_16,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_66,plain,(
    ! [A_14] :
      ( v1_xboole_0(k2_relat_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    ! [A_18] :
      ( k2_relat_1(A_18) = k1_xboole_0
      | ~ v1_xboole_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_66,c_18])).

tff(c_91,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( v5_relat_1(B_5,A_4)
      | ~ r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_106,plain,(
    ! [A_4] :
      ( v5_relat_1(k1_xboole_0,A_4)
      | ~ r1_tarski(k1_xboole_0,A_4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_8])).

tff(c_117,plain,(
    ! [A_4] : v5_relat_1(k1_xboole_0,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_16,c_106])).

tff(c_61,plain,(
    ! [A_13] :
      ( v1_funct_1(A_13)
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_65,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_6,plain,(
    ! [A_3] :
      ( v5_ordinal1(A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,
    ( ~ v5_relat_1(k1_xboole_0,'#skF_1')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_20])).

tff(c_51,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_54])).

tff(c_59,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_81,plain,(
    ~ v5_relat_1(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_59])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_81])).

%------------------------------------------------------------------------------
