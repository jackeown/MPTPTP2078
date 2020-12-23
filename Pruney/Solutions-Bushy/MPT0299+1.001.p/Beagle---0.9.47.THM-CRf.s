%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0299+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:04 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  31 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_35,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
       => r2_hidden(k4_tarski(B,A),k2_zfmisc_1(D,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_10,plain,(
    r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_9,C_10,B_11,D_12] :
      ( r2_hidden(A_9,C_10)
      | ~ r2_hidden(k4_tarski(A_9,B_11),k2_zfmisc_1(C_10,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_20,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_16])).

tff(c_11,plain,(
    ! [B_5,D_6,A_7,C_8] :
      ( r2_hidden(B_5,D_6)
      | ~ r2_hidden(k4_tarski(A_7,B_5),k2_zfmisc_1(C_8,D_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_15,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_11])).

tff(c_21,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16))
      | ~ r2_hidden(B_14,D_16)
      | ~ r2_hidden(A_13,C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_21,c_8])).

tff(c_35,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_30])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_35])).

%------------------------------------------------------------------------------
