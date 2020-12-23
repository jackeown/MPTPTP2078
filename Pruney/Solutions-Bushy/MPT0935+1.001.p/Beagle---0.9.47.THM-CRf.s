%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:06 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  28 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_mcart_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_28,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_39,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(A,B,C),k3_mcart_1(D,E,F)))) = k2_tarski(A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_mcart_1)).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : v1_relat_1(k2_tarski(k4_tarski(A_4,B_5),k4_tarski(C_6,D_7))) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_8,B_9),k4_tarski(C_10,D_11))) = k2_tarski(A_8,C_10)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_8,B_9),k4_tarski(C_10,D_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10,D_11] : k1_relat_1(k2_tarski(k4_tarski(A_8,B_9),k4_tarski(C_10,D_11))) = k2_tarski(A_8,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_tarski(k4_tarski(A_1,B_2),C_3) = k3_mcart_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_58,plain,(
    ! [A_40,B_41,C_42,D_43] : k1_relat_1(k2_tarski(k4_tarski(A_40,B_41),k4_tarski(C_42,D_43))) = k2_tarski(A_40,C_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_149,plain,(
    ! [B_66,C_67,C_65,D_64,A_68] : k1_relat_1(k2_tarski(k3_mcart_1(A_68,B_66,C_67),k4_tarski(C_65,D_64))) = k2_tarski(k4_tarski(A_68,B_66),C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_161,plain,(
    ! [B_66,C_67,B_2,C_3,A_1,A_68] : k1_relat_1(k2_tarski(k3_mcart_1(A_68,B_66,C_67),k3_mcart_1(A_1,B_2,C_3))) = k2_tarski(k4_tarski(A_68,B_66),k4_tarski(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_10,plain,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_4','#skF_5','#skF_6')))) != k2_tarski('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_181,plain,(
    k1_relat_1(k2_tarski(k4_tarski('#skF_1','#skF_2'),k4_tarski('#skF_4','#skF_5'))) != k2_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_181])).

%------------------------------------------------------------------------------
