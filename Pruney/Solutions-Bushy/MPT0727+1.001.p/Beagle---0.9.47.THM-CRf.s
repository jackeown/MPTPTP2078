%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0727+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:46 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   35 (  54 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  93 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_hidden(A,B)
          & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [C_21,B_22,A_23] :
      ( ~ v1_xboole_0(C_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(C_21))
      | ~ r2_hidden(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    ! [B_26,A_27,A_28] :
      ( ~ v1_xboole_0(B_26)
      | ~ r2_hidden(A_27,A_28)
      | ~ r1_tarski(A_28,B_26) ) ),
    inference(resolution,[status(thm)],[c_8,c_36])).

tff(c_56,plain,(
    ! [B_29] :
      ( ~ v1_xboole_0(B_29)
      | ~ r1_tarski('#skF_2',B_29) ) ),
    inference(resolution,[status(thm)],[c_16,c_49])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_56])).

tff(c_61,plain,(
    ! [A_30,C_31,B_32] :
      ( m1_subset_1(A_30,C_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_31))
      | ~ r2_hidden(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_33,B_34,A_35] :
      ( m1_subset_1(A_33,B_34)
      | ~ r2_hidden(A_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_61])).

tff(c_72,plain,(
    ! [B_36] :
      ( m1_subset_1('#skF_1',B_36)
      | ~ r1_tarski('#skF_2',B_36) ) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_76,plain,(
    m1_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [B_24,A_25] :
      ( ~ r2_hidden(B_24,A_25)
      | v1_xboole_0(B_24)
      | ~ m1_subset_1(A_25,B_24) ) ),
    inference(resolution,[status(thm)],[c_27,c_2])).

tff(c_77,plain,(
    ! [A_37,B_38] :
      ( v1_xboole_0(A_37)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_79,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_77])).

tff(c_84,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_79])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_84])).

%------------------------------------------------------------------------------
