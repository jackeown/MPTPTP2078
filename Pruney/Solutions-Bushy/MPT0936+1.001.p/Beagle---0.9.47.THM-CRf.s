%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0936+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:06 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  25 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_28,axiom,(
    ! [A,B] : v1_relat_1(k1_tarski(k4_tarski(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( C = k1_tarski(k4_tarski(A,B))
       => ( k1_relat_1(C) = k1_tarski(A)
          & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_39,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k1_tarski(k4_tarski(A_4,B_5))) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_6,B_7))) = k1_tarski(A_6)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_6,B_7] : k1_relat_1(k1_tarski(k4_tarski(A_6,B_7))) = k1_tarski(A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_34,plain,(
    ! [A_15,B_16,C_17] : k4_tarski(k4_tarski(A_15,B_16),C_17) = k3_mcart_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_43,plain,(
    ! [A_15,B_16,C_17] : k1_relat_1(k1_tarski(k3_mcart_1(A_15,B_16,C_17))) = k1_tarski(k4_tarski(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_10,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_10])).

tff(c_70,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_67])).

%------------------------------------------------------------------------------
