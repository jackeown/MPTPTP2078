%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0825+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:54 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   43 (  72 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 113 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] : r1_tarski(k6_relat_1(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).

tff(f_47,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_34,plain,(
    ~ r1_tarski(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [A_52,B_53] :
      ( r2_hidden(k4_tarski('#skF_5'(A_52,B_53),'#skF_6'(A_52,B_53)),A_52)
      | r1_tarski(A_52,B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_16])).

tff(c_81,plain,(
    ! [A_1,B_53] :
      ( '#skF_6'(k6_relat_1(A_1),B_53) = '#skF_5'(k6_relat_1(A_1),B_53)
      | r1_tarski(k6_relat_1(A_1),B_53)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_65,c_38])).

tff(c_103,plain,(
    ! [A_59,B_60] :
      ( '#skF_6'(k6_relat_1(A_59),B_60) = '#skF_5'(k6_relat_1(A_59),B_60)
      | r1_tarski(k6_relat_1(A_59),B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_81])).

tff(c_107,plain,(
    '#skF_6'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')) = '#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')) ),
    inference(resolution,[status(thm)],[c_103,c_34])).

tff(c_24,plain,(
    ! [A_9,B_19] :
      ( r2_hidden(k4_tarski('#skF_5'(A_9,B_19),'#skF_6'(A_9,B_19)),A_9)
      | r1_tarski(A_9,B_19)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,
    ( r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')),'#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7'))),k6_relat_1('#skF_7'))
    | r1_tarski(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7'))
    | ~ v1_relat_1(k6_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_24])).

tff(c_121,plain,
    ( r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')),'#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7'))),k6_relat_1('#skF_7'))
    | r1_tarski(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_114])).

tff(c_122,plain,(
    r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')),'#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7'))),k6_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_121])).

tff(c_18,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18])).

tff(c_187,plain,(
    r2_hidden('#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_122,c_36])).

tff(c_28,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( r2_hidden(k4_tarski(A_27,B_28),k2_zfmisc_1(C_29,D_30))
      | ~ r2_hidden(B_28,D_30)
      | ~ r2_hidden(A_27,C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_9,B_19] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_9,B_19),'#skF_6'(A_9,B_19)),B_19)
      | r1_tarski(A_9,B_19)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')),'#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7'))),k2_zfmisc_1('#skF_7','#skF_7'))
    | r1_tarski(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7'))
    | ~ v1_relat_1(k6_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_22])).

tff(c_118,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')),'#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7'))),k2_zfmisc_1('#skF_7','#skF_7'))
    | r1_tarski(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_111])).

tff(c_119,plain,(
    ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')),'#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7'))),k2_zfmisc_1('#skF_7','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_118])).

tff(c_335,plain,(
    ~ r2_hidden('#skF_5'(k6_relat_1('#skF_7'),k2_zfmisc_1('#skF_7','#skF_7')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_119])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_335])).

%------------------------------------------------------------------------------
