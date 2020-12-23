%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0448+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:19 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_30,axiom,(
    ! [A,B] : v1_relat_1(k1_tarski(k4_tarski(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( C = k1_tarski(k4_tarski(A,B))
       => ( k1_relat_1(C) = k1_tarski(A)
          & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_4,plain,(
    ! [A_2,B_3] : v1_relat_1(k1_tarski(k4_tarski(A_2,B_3))) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_4,B_5))) = k1_tarski(A_4)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_4,B_5] : k1_relat_1(k1_tarski(k4_tarski(A_4,B_5))) = k1_tarski(A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k2_relat_1(k1_tarski(k4_tarski(A_4,B_5))) = k1_tarski(B_5)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_4,B_5] : k2_relat_1(k1_tarski(k4_tarski(A_4,B_5))) = k1_tarski(B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_45,plain,(
    ! [A_17] :
      ( k2_xboole_0(k1_relat_1(A_17),k2_relat_1(A_17)) = k3_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_54,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(A_4,B_5))),k1_tarski(B_5)) = k3_relat_1(k1_tarski(k4_tarski(A_4,B_5)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_4,B_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_45])).

tff(c_61,plain,(
    ! [A_4,B_5] : k3_relat_1(k1_tarski(k4_tarski(A_4,B_5))) = k2_tarski(A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10,c_14,c_54])).

tff(c_12,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_12])).

%------------------------------------------------------------------------------
