%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1086+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:23 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   15 (  17 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   15 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_finset_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_37,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_finset_1(A)
          & v1_finset_1(B) )
       => v1_finset_1(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_finset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_finset_1)).

tff(c_8,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    v1_finset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9,plain,(
    ! [A_3,B_4] :
      ( v1_finset_1(k2_xboole_0(A_3,B_4))
      | ~ v1_finset_1(B_4)
      | ~ v1_finset_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4,plain,(
    ~ v1_finset_1(k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,
    ( ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_9,c_4])).

tff(c_16,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_12])).

%------------------------------------------------------------------------------
