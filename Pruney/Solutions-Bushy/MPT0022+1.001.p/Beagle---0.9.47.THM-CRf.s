%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0022+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:35 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   31 (  62 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  73 expanded)
%              Number of equality atoms :   15 (  36 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(A,B) = k1_xboole_0
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_14,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_39,plain,(
    ! [B_7,A_8] :
      ( ~ v1_xboole_0(k2_xboole_0(B_7,A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_39])).

tff(c_48,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_45])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_10])).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,(
    ! [A_3] : k2_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_54,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_83,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_54])).

tff(c_85,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_83])).

%------------------------------------------------------------------------------
