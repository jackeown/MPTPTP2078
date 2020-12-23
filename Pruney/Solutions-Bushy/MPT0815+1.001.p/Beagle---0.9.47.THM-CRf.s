%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0815+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:53 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_30,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_20,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( r2_hidden(k4_tarski(A_25,B_26),k2_zfmisc_1(C_27,D_28))
      | ~ r2_hidden(B_26,D_28)
      | ~ r2_hidden(A_25,C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_1','#skF_3')),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_14,c_16])).

tff(c_40,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_36])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_40])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_52])).

%------------------------------------------------------------------------------
