%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0420+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:17 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  92 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 194 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(k7_setfam_1(A,B),C)
            <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

tff(c_12,plain,
    ( ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_19,plain,(
    ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_18,plain,
    ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_3')
    | r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_18])).

tff(c_8,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_21,plain,(
    ! [A_10,B_11] :
      ( k7_setfam_1(A_10,k7_setfam_1(A_10,B_11)) = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_21])).

tff(c_48,plain,(
    ! [B_14,C_15,A_16] :
      ( r1_tarski(B_14,C_15)
      | ~ r1_tarski(k7_setfam_1(A_16,B_14),k7_setfam_1(A_16,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k1_zfmisc_1(A_16)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [C_15] :
      ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),C_15)
      | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1',C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_48])).

tff(c_133,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_136,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_151,plain,(
    ! [C_21] :
      ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),C_21)
      | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1',C_21))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_161,plain,
    ( r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_3')
    | ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_170,plain,(
    r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_161])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_170])).

tff(c_173,plain,(
    ~ r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_174,plain,(
    r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_177,plain,(
    ! [A_22,B_23] :
      ( k7_setfam_1(A_22,k7_setfam_1(A_22,B_23)) = B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_182,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_270,plain,(
    ! [B_30,C_31,A_32] :
      ( r1_tarski(B_30,C_31)
      | ~ r1_tarski(k7_setfam_1(A_32,B_30),k7_setfam_1(A_32,C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_zfmisc_1(A_32)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_285,plain,(
    ! [C_31] :
      ( r1_tarski(k7_setfam_1('#skF_1','#skF_3'),C_31)
      | ~ r1_tarski('#skF_3',k7_setfam_1('#skF_1',C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_270])).

tff(c_307,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_310,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_307])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_310])).

tff(c_316,plain,(
    m1_subset_1(k7_setfam_1('#skF_1','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_288,plain,(
    ! [B_30] :
      ( r1_tarski(B_30,k7_setfam_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k7_setfam_1('#skF_1',B_30),'#skF_3')
      | ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_270])).

tff(c_411,plain,(
    ! [B_36] :
      ( r1_tarski(B_36,k7_setfam_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k7_setfam_1('#skF_1',B_36),'#skF_3')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_288])).

tff(c_427,plain,
    ( r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k7_setfam_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_411])).

tff(c_438,plain,(
    r1_tarski('#skF_2',k7_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_427])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_438])).

%------------------------------------------------------------------------------
