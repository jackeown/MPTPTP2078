%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0254+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:35:59 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_31,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_27,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_28,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_41,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(c_8,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_tarski(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_13,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_12,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_29,plain,(
    ! [B_9,A_10] : k2_xboole_0(B_9,A_10) = k2_xboole_0(A_10,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_71,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(k2_xboole_0(B_5,A_4))
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_87,plain,(
    v1_xboole_0(k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13,c_83])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_87])).

%------------------------------------------------------------------------------
