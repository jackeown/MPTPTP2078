%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0865+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:58 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  50 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,B)
         => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_16] :
      ( k4_tarski('#skF_2'(A_1,B_16),'#skF_3'(A_1,B_16)) = B_16
      | ~ r2_hidden(B_16,A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_43,plain,(
    ! [A_30,B_31] :
      ( k4_tarski('#skF_2'(A_30,B_31),'#skF_3'(A_30,B_31)) = B_31
      | ~ r2_hidden(B_31,A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [B_22,C_23] : k4_tarski(k1_mcart_1(k4_tarski(B_22,C_23)),k2_mcart_1(k4_tarski(B_22,C_23))) = k4_tarski(B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [B_37,A_38] :
      ( k4_tarski(k1_mcart_1(B_37),k2_mcart_1(k4_tarski('#skF_2'(A_38,B_37),'#skF_3'(A_38,B_37)))) = k4_tarski('#skF_2'(A_38,B_37),'#skF_3'(A_38,B_37))
      | ~ r2_hidden(B_37,A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_8])).

tff(c_88,plain,(
    ! [B_39,A_40] :
      ( k4_tarski(k1_mcart_1(B_39),k2_mcart_1(B_39)) = k4_tarski('#skF_2'(A_40,B_39),'#skF_3'(A_40,B_39))
      | ~ r2_hidden(B_39,A_40)
      | ~ v1_relat_1(A_40)
      | ~ r2_hidden(B_39,A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_10,plain,(
    k4_tarski(k1_mcart_1('#skF_4'),k2_mcart_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,(
    ! [A_41] :
      ( k4_tarski('#skF_2'(A_41,'#skF_4'),'#skF_3'(A_41,'#skF_4')) != '#skF_4'
      | ~ r2_hidden('#skF_4',A_41)
      | ~ v1_relat_1(A_41)
      | ~ r2_hidden('#skF_4',A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_10])).

tff(c_145,plain,(
    ! [A_42] :
      ( ~ r2_hidden('#skF_4',A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_148,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_148])).

%------------------------------------------------------------------------------
