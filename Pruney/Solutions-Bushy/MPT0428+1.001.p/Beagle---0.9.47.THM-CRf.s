%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0428+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:17 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 108 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_22,plain,
    ( k5_setfam_1('#skF_1','#skF_2') != '#skF_1'
    | ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( m1_setfam_1('#skF_2','#skF_1')
    | k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    ! [A_23,B_24] :
      ( k5_setfam_1(A_23,B_24) = k3_tarski(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_83,plain,(
    k3_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    ! [B_14,A_15] :
      ( m1_setfam_1(B_14,A_15)
      | ~ r1_tarski(A_15,k3_tarski(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41,plain,(
    ! [B_14] : m1_setfam_1(B_14,k3_tarski(B_14)) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_87,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_41])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_87])).

tff(c_98,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_98])).

tff(c_102,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ m1_setfam_1(B_4,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_122,plain,(
    ! [A_27,B_28] :
      ( k5_setfam_1(A_27,B_28) = k3_tarski(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_131,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_122])).

tff(c_101,plain,(
    k5_setfam_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_132,plain,(
    k3_tarski('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_101])).

tff(c_157,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k5_setfam_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_157])).

tff(c_174,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_170])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_178,plain,(
    r1_tarski(k3_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_174,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_180,plain,
    ( k3_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_178,c_2])).

tff(c_183,plain,(
    ~ r1_tarski('#skF_1',k3_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_180])).

tff(c_186,plain,(
    ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_183])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_186])).

%------------------------------------------------------------------------------
