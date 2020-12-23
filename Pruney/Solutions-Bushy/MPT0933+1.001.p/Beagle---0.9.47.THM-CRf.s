%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0933+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:06 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  35 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  69 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( ( r2_hidden(C,B)
              & r2_hidden(A,B)
              & k1_mcart_1(C) = k1_mcart_1(A)
              & k2_mcart_1(C) = k2_mcart_1(A) )
           => C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(c_4,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_23,plain,(
    ! [A_4,B_5] :
      ( k4_tarski(k1_mcart_1(A_4),k2_mcart_1(A_4)) = A_4
      | ~ r2_hidden(A_4,B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_25,plain,
    ( k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_23])).

tff(c_30,plain,(
    k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_25])).

tff(c_6,plain,(
    k2_mcart_1('#skF_3') = k2_mcart_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    k1_mcart_1('#skF_3') = k1_mcart_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_27,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_33,plain,(
    k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6,c_8,c_27])).

tff(c_38,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_33])).

tff(c_39,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_38])).

%------------------------------------------------------------------------------
