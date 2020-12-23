%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0421+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:17 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  33 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_setfam_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( k7_setfam_1(A,B) = k7_setfam_1(A,C)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_setfam_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_4,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15,plain,(
    ! [A_4,B_5] :
      ( k7_setfam_1(A_4,k7_setfam_1(A_4,B_5)) = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_20,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_15])).

tff(c_6,plain,(
    k7_setfam_1('#skF_1','#skF_2') = k7_setfam_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_15])).

tff(c_22,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19])).

tff(c_27,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_28,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_27])).

%------------------------------------------------------------------------------
