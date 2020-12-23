%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:03 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  177 (1233 expanded)
%              Number of leaves         :   23 ( 401 expanded)
%              Depth                    :   13
%              Number of atoms          :  246 (2796 expanded)
%              Number of equality atoms :   98 ( 954 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_91,plain,(
    ! [A_31,B_32] :
      ( k6_setfam_1(A_31,B_32) = k1_setfam_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_103,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_718,plain,(
    ! [A_67,B_68] :
      ( k8_setfam_1(A_67,B_68) = k6_setfam_1(A_67,B_68)
      | k1_xboole_0 = B_68
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_729,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_718])).

tff(c_736,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_729])).

tff(c_972,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_461,plain,(
    ! [A_60,B_61] :
      ( k8_setfam_1(A_60,B_61) = k6_setfam_1(A_60,B_61)
      | k1_xboole_0 = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_472,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_461])).

tff(c_479,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_472])).

tff(c_482,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_104,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_91])).

tff(c_475,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_461])).

tff(c_481,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_475])).

tff(c_506,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_481])).

tff(c_507,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_513,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_26])).

tff(c_163,plain,(
    ! [A_44,B_45] :
      ( k8_setfam_1(A_44,B_45) = k6_setfam_1(A_44,B_45)
      | k1_xboole_0 = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_174,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_181,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_174])).

tff(c_185,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_177,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_163])).

tff(c_183,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_177])).

tff(c_229,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_183])).

tff(c_230,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_242,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_26])).

tff(c_6,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_xboole_0(A_25,C_26)
      | ~ r1_xboole_0(B_27,C_26)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_28] :
      ( r1_xboole_0(A_28,k1_xboole_0)
      | ~ r1_tarski(A_28,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    ! [A_38,A_39] :
      ( r1_xboole_0(A_38,k1_xboole_0)
      | ~ r1_tarski(A_38,A_39)
      | ~ r1_tarski(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_138,plain,
    ( r1_xboole_0('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_139,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_190,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_139])).

tff(c_235,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_190])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_235])).

tff(c_263,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k8_setfam_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_269,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_14])).

tff(c_273,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_269])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_278,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_273,c_18])).

tff(c_43,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    ! [A_30] :
      ( k8_setfam_1(A_30,k1_xboole_0) = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    ! [A_30] :
      ( k8_setfam_1(A_30,k1_xboole_0) = A_30
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_291,plain,(
    ! [A_51] :
      ( k8_setfam_1(A_51,'#skF_2') = A_51
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(A_51)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_90])).

tff(c_295,plain,(
    k8_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_291])).

tff(c_24,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_265,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_24])).

tff(c_296,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_265])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_296])).

tff(c_301,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_setfam_1(B_16),k1_setfam_1(A_15))
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_319,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_320,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_301])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_29] :
      ( r1_xboole_0(k1_xboole_0,A_29)
      | ~ r1_tarski(A_29,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_151,plain,(
    ! [A_42,A_43] :
      ( r1_xboole_0(A_42,A_43)
      | ~ r1_tarski(A_42,k1_xboole_0)
      | ~ r1_tarski(A_43,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_73,c_4])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(A_6,A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_162,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ r1_tarski(A_43,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_151,c_8])).

tff(c_351,plain,(
    ! [A_53] :
      ( A_53 = '#skF_3'
      | ~ r1_tarski(A_53,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_319,c_162])).

tff(c_354,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_351])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_354])).

tff(c_359,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_300,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_302,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_24])).

tff(c_361,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_302])).

tff(c_373,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_361])).

tff(c_376,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_373])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_376])).

tff(c_380,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_69,plain,(
    ! [A_3,A_28] :
      ( r1_xboole_0(A_3,k1_xboole_0)
      | ~ r1_tarski(A_3,A_28)
      | ~ r1_tarski(A_28,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_389,plain,
    ( r1_xboole_0('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_380,c_69])).

tff(c_420,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_489,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_482,c_420])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_507,c_507,c_489])).

tff(c_545,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_566,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_14])).

tff(c_570,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_566])).

tff(c_575,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_570,c_18])).

tff(c_600,plain,(
    ! [A_66] :
      ( k8_setfam_1(A_66,'#skF_2') = A_66
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(A_66)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_482,c_90])).

tff(c_604,plain,(
    k8_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_600])).

tff(c_562,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_24])).

tff(c_605,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_562])).

tff(c_608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_605])).

tff(c_610,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_628,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_481])).

tff(c_379,plain,(
    r1_xboole_0('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_386,plain,(
    r1_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_379,c_2])).

tff(c_435,plain,(
    ! [A_58] :
      ( r1_xboole_0(A_58,'#skF_2')
      | ~ r1_tarski(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_386,c_4])).

tff(c_446,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_435,c_8])).

tff(c_447,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_633,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_447])).

tff(c_651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_633])).

tff(c_652,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_481])).

tff(c_609,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_611,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_24])).

tff(c_654,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_611])).

tff(c_666,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_654])).

tff(c_669,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_666])).

tff(c_671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_669])).

tff(c_672,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_673,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_693,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_673])).

tff(c_676,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_672,c_420])).

tff(c_704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_676])).

tff(c_706,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_980,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_972,c_706])).

tff(c_759,plain,(
    ! [A_70] :
      ( r1_xboole_0(A_70,'#skF_2')
      | ~ r1_tarski(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_386,c_4])).

tff(c_770,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_759,c_8])).

tff(c_958,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_974,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_958])).

tff(c_1030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_974])).

tff(c_1032,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_1031,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_55,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_732,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_718])).

tff(c_738,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_732])).

tff(c_771,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_738])).

tff(c_881,plain,(
    ! [A_74] :
      ( k8_setfam_1(A_74,'#skF_3') = A_74
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_74)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_771,c_90])).

tff(c_885,plain,(
    k8_setfam_1('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_55,c_881])).

tff(c_823,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_736])).

tff(c_824,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_823])).

tff(c_828,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_24])).

tff(c_886,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_885,c_828])).

tff(c_890,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_885,c_14])).

tff(c_894,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_890])).

tff(c_898,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_894,c_18])).

tff(c_902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_886,c_898])).

tff(c_904,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_823])).

tff(c_937,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_771,c_771,c_770])).

tff(c_938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_904,c_937])).

tff(c_939,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_738])).

tff(c_941,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_24])).

tff(c_1034,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_941])).

tff(c_1046,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1034])).

tff(c_1049,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1046])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1032,c_1049])).

tff(c_1052,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_940,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_738])).

tff(c_1054,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_940])).

tff(c_1063,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_380])).

tff(c_705,plain,(
    r1_xboole_0('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_712,plain,(
    r1_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_705,c_2])).

tff(c_743,plain,(
    ! [A_3] :
      ( r1_xboole_0(A_3,'#skF_3')
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_712,c_4])).

tff(c_1205,plain,(
    ! [A_87] :
      ( r1_xboole_0(A_87,'#skF_3')
      | ~ r1_tarski(A_87,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_743])).

tff(c_1071,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(A_6,A_6)
      | A_6 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_8])).

tff(c_1209,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1205,c_1071])).

tff(c_1216,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1209])).

tff(c_1218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1054,c_1216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:24:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.54  
% 3.28/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.54  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.28/1.54  
% 3.28/1.54  %Foreground sorts:
% 3.28/1.54  
% 3.28/1.54  
% 3.28/1.54  %Background operators:
% 3.28/1.54  
% 3.28/1.54  
% 3.28/1.54  %Foreground operators:
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.54  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.28/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.28/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.54  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.28/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.28/1.54  
% 3.28/1.56  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.28/1.56  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.28/1.56  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.28/1.56  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.28/1.56  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.28/1.56  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.28/1.56  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.28/1.56  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.28/1.56  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.28/1.56  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.28/1.56  tff(c_91, plain, (![A_31, B_32]: (k6_setfam_1(A_31, B_32)=k1_setfam_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.56  tff(c_103, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_91])).
% 3.28/1.56  tff(c_718, plain, (![A_67, B_68]: (k8_setfam_1(A_67, B_68)=k6_setfam_1(A_67, B_68) | k1_xboole_0=B_68 | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.56  tff(c_729, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_718])).
% 3.28/1.56  tff(c_736, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_729])).
% 3.28/1.56  tff(c_972, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_736])).
% 3.28/1.56  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.28/1.56  tff(c_461, plain, (![A_60, B_61]: (k8_setfam_1(A_60, B_61)=k6_setfam_1(A_60, B_61) | k1_xboole_0=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.56  tff(c_472, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_461])).
% 3.28/1.56  tff(c_479, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_472])).
% 3.28/1.56  tff(c_482, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_479])).
% 3.28/1.56  tff(c_104, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_91])).
% 3.28/1.56  tff(c_475, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_461])).
% 3.28/1.56  tff(c_481, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_475])).
% 3.28/1.56  tff(c_506, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_481])).
% 3.28/1.56  tff(c_507, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_506])).
% 3.28/1.56  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.28/1.56  tff(c_513, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_26])).
% 3.28/1.56  tff(c_163, plain, (![A_44, B_45]: (k8_setfam_1(A_44, B_45)=k6_setfam_1(A_44, B_45) | k1_xboole_0=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.56  tff(c_174, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_163])).
% 3.28/1.56  tff(c_181, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_174])).
% 3.28/1.56  tff(c_185, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_181])).
% 3.28/1.56  tff(c_177, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_163])).
% 3.28/1.56  tff(c_183, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_177])).
% 3.28/1.56  tff(c_229, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_183])).
% 3.28/1.56  tff(c_230, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_229])).
% 3.28/1.56  tff(c_242, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_26])).
% 3.28/1.56  tff(c_6, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.56  tff(c_56, plain, (![A_25, C_26, B_27]: (r1_xboole_0(A_25, C_26) | ~r1_xboole_0(B_27, C_26) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.56  tff(c_60, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0) | ~r1_tarski(A_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_56])).
% 3.28/1.56  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.56  tff(c_126, plain, (![A_38, A_39]: (r1_xboole_0(A_38, k1_xboole_0) | ~r1_tarski(A_38, A_39) | ~r1_tarski(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_60, c_4])).
% 3.28/1.56  tff(c_138, plain, (r1_xboole_0('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_126])).
% 3.28/1.56  tff(c_139, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_138])).
% 3.28/1.56  tff(c_190, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_139])).
% 3.28/1.56  tff(c_235, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_190])).
% 3.28/1.56  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_235])).
% 3.28/1.56  tff(c_263, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_229])).
% 3.28/1.56  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k8_setfam_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.28/1.56  tff(c_269, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_263, c_14])).
% 3.28/1.56  tff(c_273, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_269])).
% 3.28/1.56  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.28/1.56  tff(c_278, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_273, c_18])).
% 3.28/1.56  tff(c_43, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.28/1.56  tff(c_54, plain, (r1_tarski('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_43])).
% 3.28/1.56  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.28/1.56  tff(c_86, plain, (![A_30]: (k8_setfam_1(A_30, k1_xboole_0)=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.56  tff(c_90, plain, (![A_30]: (k8_setfam_1(A_30, k1_xboole_0)=A_30 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_20, c_86])).
% 3.28/1.56  tff(c_291, plain, (![A_51]: (k8_setfam_1(A_51, '#skF_2')=A_51 | ~r1_tarski('#skF_2', k1_zfmisc_1(A_51)))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_90])).
% 3.28/1.56  tff(c_295, plain, (k8_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_54, c_291])).
% 3.28/1.56  tff(c_24, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.28/1.56  tff(c_265, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_24])).
% 3.28/1.56  tff(c_296, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_265])).
% 3.28/1.56  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_296])).
% 3.28/1.56  tff(c_301, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_181])).
% 3.28/1.56  tff(c_22, plain, (![B_16, A_15]: (r1_tarski(k1_setfam_1(B_16), k1_setfam_1(A_15)) | k1_xboole_0=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.28/1.56  tff(c_319, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_183])).
% 3.28/1.56  tff(c_320, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_319, c_301])).
% 3.28/1.56  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.28/1.56  tff(c_73, plain, (![A_29]: (r1_xboole_0(k1_xboole_0, A_29) | ~r1_tarski(A_29, k1_xboole_0))), inference(resolution, [status(thm)], [c_60, c_2])).
% 3.28/1.56  tff(c_151, plain, (![A_42, A_43]: (r1_xboole_0(A_42, A_43) | ~r1_tarski(A_42, k1_xboole_0) | ~r1_tarski(A_43, k1_xboole_0))), inference(resolution, [status(thm)], [c_73, c_4])).
% 3.28/1.56  tff(c_8, plain, (![A_6]: (~r1_xboole_0(A_6, A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.56  tff(c_162, plain, (![A_43]: (k1_xboole_0=A_43 | ~r1_tarski(A_43, k1_xboole_0))), inference(resolution, [status(thm)], [c_151, c_8])).
% 3.28/1.56  tff(c_351, plain, (![A_53]: (A_53='#skF_3' | ~r1_tarski(A_53, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_319, c_162])).
% 3.28/1.56  tff(c_354, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_26, c_351])).
% 3.28/1.56  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_354])).
% 3.28/1.56  tff(c_359, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_183])).
% 3.28/1.56  tff(c_300, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_181])).
% 3.28/1.56  tff(c_302, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_24])).
% 3.28/1.56  tff(c_361, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_302])).
% 3.28/1.56  tff(c_373, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_361])).
% 3.28/1.56  tff(c_376, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_373])).
% 3.28/1.56  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301, c_376])).
% 3.28/1.56  tff(c_380, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 3.28/1.56  tff(c_69, plain, (![A_3, A_28]: (r1_xboole_0(A_3, k1_xboole_0) | ~r1_tarski(A_3, A_28) | ~r1_tarski(A_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_60, c_4])).
% 3.28/1.56  tff(c_389, plain, (r1_xboole_0('#skF_3', k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_380, c_69])).
% 3.28/1.56  tff(c_420, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_389])).
% 3.28/1.56  tff(c_489, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_482, c_482, c_420])).
% 3.28/1.56  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_513, c_507, c_507, c_489])).
% 3.28/1.56  tff(c_545, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_506])).
% 3.28/1.56  tff(c_566, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_545, c_14])).
% 3.28/1.56  tff(c_570, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_566])).
% 3.28/1.56  tff(c_575, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_570, c_18])).
% 3.28/1.56  tff(c_600, plain, (![A_66]: (k8_setfam_1(A_66, '#skF_2')=A_66 | ~r1_tarski('#skF_2', k1_zfmisc_1(A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_482, c_90])).
% 3.28/1.56  tff(c_604, plain, (k8_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_54, c_600])).
% 3.28/1.56  tff(c_562, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_24])).
% 3.28/1.56  tff(c_605, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_562])).
% 3.28/1.56  tff(c_608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_575, c_605])).
% 3.28/1.56  tff(c_610, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_479])).
% 3.28/1.56  tff(c_628, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_481])).
% 3.28/1.56  tff(c_379, plain, (r1_xboole_0('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 3.28/1.56  tff(c_386, plain, (r1_xboole_0(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_379, c_2])).
% 3.28/1.56  tff(c_435, plain, (![A_58]: (r1_xboole_0(A_58, '#skF_2') | ~r1_tarski(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_386, c_4])).
% 3.28/1.56  tff(c_446, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_435, c_8])).
% 3.28/1.56  tff(c_447, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_446])).
% 3.28/1.56  tff(c_633, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_628, c_447])).
% 3.28/1.56  tff(c_651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_633])).
% 3.28/1.56  tff(c_652, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_481])).
% 3.28/1.56  tff(c_609, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_479])).
% 3.28/1.56  tff(c_611, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_609, c_24])).
% 3.28/1.56  tff(c_654, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_611])).
% 3.28/1.56  tff(c_666, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_654])).
% 3.28/1.56  tff(c_669, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_666])).
% 3.28/1.56  tff(c_671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_610, c_669])).
% 3.28/1.56  tff(c_672, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_446])).
% 3.28/1.56  tff(c_673, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_446])).
% 3.28/1.56  tff(c_693, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_672, c_673])).
% 3.28/1.56  tff(c_676, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_672, c_672, c_420])).
% 3.28/1.56  tff(c_704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_693, c_676])).
% 3.28/1.56  tff(c_706, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_389])).
% 3.28/1.56  tff(c_980, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_972, c_972, c_706])).
% 3.28/1.56  tff(c_759, plain, (![A_70]: (r1_xboole_0(A_70, '#skF_2') | ~r1_tarski(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_386, c_4])).
% 3.28/1.56  tff(c_770, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_759, c_8])).
% 3.28/1.56  tff(c_958, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_770])).
% 3.28/1.56  tff(c_974, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_972, c_958])).
% 3.28/1.56  tff(c_1030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_980, c_974])).
% 3.28/1.56  tff(c_1032, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_736])).
% 3.28/1.56  tff(c_1031, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_736])).
% 3.28/1.56  tff(c_55, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_43])).
% 3.28/1.56  tff(c_732, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_718])).
% 3.28/1.56  tff(c_738, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_732])).
% 3.28/1.56  tff(c_771, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_738])).
% 3.28/1.56  tff(c_881, plain, (![A_74]: (k8_setfam_1(A_74, '#skF_3')=A_74 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_74)))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_771, c_90])).
% 3.28/1.56  tff(c_885, plain, (k8_setfam_1('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_55, c_881])).
% 3.28/1.56  tff(c_823, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_771, c_736])).
% 3.28/1.56  tff(c_824, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_823])).
% 3.28/1.56  tff(c_828, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_824, c_24])).
% 3.28/1.56  tff(c_886, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_885, c_885, c_828])).
% 3.28/1.56  tff(c_890, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_885, c_14])).
% 3.28/1.56  tff(c_894, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_890])).
% 3.28/1.56  tff(c_898, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_894, c_18])).
% 3.28/1.56  tff(c_902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_886, c_898])).
% 3.28/1.56  tff(c_904, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_823])).
% 3.28/1.56  tff(c_937, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_771, c_771, c_770])).
% 3.28/1.56  tff(c_938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_904, c_937])).
% 3.28/1.56  tff(c_939, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_738])).
% 3.28/1.56  tff(c_941, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_939, c_24])).
% 3.28/1.56  tff(c_1034, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_941])).
% 3.28/1.56  tff(c_1046, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_1034])).
% 3.28/1.56  tff(c_1049, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1046])).
% 3.28/1.56  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1032, c_1049])).
% 3.28/1.56  tff(c_1052, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_770])).
% 3.28/1.56  tff(c_940, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_738])).
% 3.28/1.56  tff(c_1054, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_940])).
% 3.28/1.56  tff(c_1063, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_380])).
% 3.28/1.56  tff(c_705, plain, (r1_xboole_0('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_389])).
% 3.28/1.56  tff(c_712, plain, (r1_xboole_0(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_705, c_2])).
% 3.28/1.56  tff(c_743, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_3') | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_712, c_4])).
% 3.28/1.56  tff(c_1205, plain, (![A_87]: (r1_xboole_0(A_87, '#skF_3') | ~r1_tarski(A_87, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_743])).
% 3.28/1.56  tff(c_1071, plain, (![A_6]: (~r1_xboole_0(A_6, A_6) | A_6='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_8])).
% 3.28/1.56  tff(c_1209, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1205, c_1071])).
% 3.28/1.56  tff(c_1216, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1209])).
% 3.28/1.56  tff(c_1218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1054, c_1216])).
% 3.28/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.56  
% 3.28/1.56  Inference rules
% 3.28/1.56  ----------------------
% 3.28/1.56  #Ref     : 0
% 3.28/1.56  #Sup     : 226
% 3.28/1.56  #Fact    : 0
% 3.28/1.56  #Define  : 0
% 3.28/1.56  #Split   : 17
% 3.28/1.56  #Chain   : 0
% 3.28/1.56  #Close   : 0
% 3.28/1.56  
% 3.28/1.56  Ordering : KBO
% 3.28/1.56  
% 3.28/1.56  Simplification rules
% 3.28/1.56  ----------------------
% 3.28/1.56  #Subsume      : 33
% 3.28/1.56  #Demod        : 382
% 3.28/1.56  #Tautology    : 128
% 3.28/1.56  #SimpNegUnit  : 8
% 3.28/1.56  #BackRed      : 176
% 3.28/1.56  
% 3.28/1.56  #Partial instantiations: 0
% 3.28/1.56  #Strategies tried      : 1
% 3.28/1.56  
% 3.28/1.56  Timing (in seconds)
% 3.28/1.56  ----------------------
% 3.68/1.57  Preprocessing        : 0.31
% 3.68/1.57  Parsing              : 0.16
% 3.68/1.57  CNF conversion       : 0.02
% 3.68/1.57  Main loop            : 0.47
% 3.68/1.57  Inferencing          : 0.15
% 3.68/1.57  Reduction            : 0.15
% 3.68/1.57  Demodulation         : 0.10
% 3.68/1.57  BG Simplification    : 0.02
% 3.68/1.57  Subsumption          : 0.10
% 3.68/1.57  Abstraction          : 0.02
% 3.68/1.57  MUC search           : 0.00
% 3.68/1.57  Cooper               : 0.00
% 3.68/1.57  Total                : 0.84
% 3.68/1.57  Index Insertion      : 0.00
% 3.68/1.57  Index Deletion       : 0.00
% 3.68/1.57  Index Matching       : 0.00
% 3.68/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
