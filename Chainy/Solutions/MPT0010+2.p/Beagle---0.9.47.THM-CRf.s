%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0010+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:09 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   51 (  62 expanded)
%              Number of leaves         :   38 (  43 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  42 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_18 > #skF_6 > #skF_1 > #skF_17 > #skF_19 > #skF_4 > #skF_10 > #skF_12 > #skF_5 > #skF_9 > #skF_7 > #skF_14 > #skF_3 > #skF_2 > #skF_8 > #skF_16 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * ( $i * $i ) ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * ( $i * $i ) ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * ( $i * $i ) ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * ( $i * $i ) ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * ( $i * $i ) ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * ( $i * $i ) ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * ( $i * $i ) ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(f_136,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',rc1_xboole_0)).

tff(f_259,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_255,negated_conjecture,(
    ~ ! [A] :
        ( r1_tarski(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_250,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_242,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_112,plain,(
    v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_239,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_248,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_112,c_239])).

tff(c_202,plain,(
    k1_xboole_0 != '#skF_19' ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_254,plain,(
    '#skF_19' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_202])).

tff(c_200,plain,(
    ! [A_86] : r1_tarski(k1_xboole_0,A_86) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_251,plain,(
    ! [A_86] : r1_tarski('#skF_9',A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_200])).

tff(c_204,plain,(
    r1_tarski('#skF_19',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_250,plain,(
    r1_tarski('#skF_19','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_204])).

tff(c_757,plain,(
    ! [B_175,A_176] :
      ( B_175 = A_176
      | ~ r1_tarski(B_175,A_176)
      | ~ r1_tarski(A_176,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_763,plain,
    ( '#skF_19' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_19') ),
    inference(resolution,[status(thm)],[c_250,c_757])).

tff(c_770,plain,(
    '#skF_19' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_763])).

tff(c_772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_770])).
%------------------------------------------------------------------------------
