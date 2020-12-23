%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0602+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:34 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(f_28,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_33,negated_conjecture,(
    ~ ! [A,B] :
        ( v4_relat_1(k1_xboole_0,A)
        & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).

tff(c_2,plain,(
    ! [A_1] : v4_relat_1(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4,plain,(
    ! [B_2] : v5_relat_1(k1_xboole_0,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,
    ( ~ v4_relat_1(k1_xboole_0,'#skF_2')
    | ~ v5_relat_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ~ v4_relat_1(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_10,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

%------------------------------------------------------------------------------
