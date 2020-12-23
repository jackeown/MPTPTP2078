%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:58 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 410 expanded)
%              Number of leaves         :   42 ( 158 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 873 expanded)
%              Number of equality atoms :   37 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_44,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_149,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_149])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_152])).

tff(c_46,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k9_relat_1(B_29,A_28),k2_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_24,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2347,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k7_relset_1(A_241,B_242,C_243,D_244) = k9_relat_1(C_243,D_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2360,plain,(
    ! [D_244] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_244) = k9_relat_1('#skF_4',D_244) ),
    inference(resolution,[status(thm)],[c_66,c_2347])).

tff(c_2423,plain,(
    ! [B_254,A_255] :
      ( k1_tarski(k1_funct_1(B_254,A_255)) = k2_relat_1(B_254)
      | k1_tarski(A_255) != k1_relat_1(B_254)
      | ~ v1_funct_1(B_254)
      | ~ v1_relat_1(B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2432,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2423,c_62])).

tff(c_2438,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_70,c_2432])).

tff(c_2461,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_2438])).

tff(c_2462,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2461])).

tff(c_248,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_266,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_248])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_269,plain,(
    ! [B_79,A_80] :
      ( k1_tarski(B_79) = A_80
      | k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,k1_tarski(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3932,plain,(
    ! [B_359,B_360] :
      ( k1_tarski(B_359) = k1_relat_1(B_360)
      | k1_relat_1(B_360) = k1_xboole_0
      | ~ v4_relat_1(B_360,k1_tarski(B_359))
      | ~ v1_relat_1(B_360) ) ),
    inference(resolution,[status(thm)],[c_38,c_269])).

tff(c_3970,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_266,c_3932])).

tff(c_3987,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3970])).

tff(c_3988,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2462,c_3987])).

tff(c_56,plain,(
    ! [B_40,A_39] :
      ( m1_subset_1(B_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_40),A_39)))
      | ~ r1_tarski(k2_relat_1(B_40),A_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4026,plain,(
    ! [A_39] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_39)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_39)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3988,c_56])).

tff(c_4062,plain,(
    ! [A_39] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_70,c_24,c_4026])).

tff(c_4147,plain,(
    ! [A_368] : ~ r1_tarski(k2_relat_1('#skF_4'),A_368) ),
    inference(splitLeft,[status(thm)],[c_4062])).

tff(c_4159,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_4147])).

tff(c_4160,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4062])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4186,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4160,c_28])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_26,c_113])).

tff(c_181,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_117,c_181])).

tff(c_4338,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4186,c_189])).

tff(c_4402,plain,(
    ! [A_13] : r1_tarski('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4338,c_117])).

tff(c_22,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [A_45,B_46] : v1_relat_1(k2_zfmisc_1(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_97])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_314,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_407,plain,(
    ! [A_101,B_102,A_103] :
      ( v5_relat_1(A_101,B_102)
      | ~ r1_tarski(A_101,k2_zfmisc_1(A_103,B_102)) ) ),
    inference(resolution,[status(thm)],[c_30,c_314])).

tff(c_439,plain,(
    ! [A_103,B_102] : v5_relat_1(k2_zfmisc_1(A_103,B_102),B_102) ),
    inference(resolution,[status(thm)],[c_6,c_407])).

tff(c_385,plain,(
    ! [B_99,A_100] :
      ( r1_tarski(k2_relat_1(B_99),A_100)
      | ~ v5_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_509,plain,(
    ! [B_116] :
      ( k2_relat_1(B_116) = k1_xboole_0
      | ~ v5_relat_1(B_116,k1_xboole_0)
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_385,c_189])).

tff(c_513,plain,(
    ! [A_103] :
      ( k2_relat_1(k2_zfmisc_1(A_103,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_103,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_439,c_509])).

tff(c_524,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_22,c_22,c_513])).

tff(c_541,plain,(
    ! [A_28] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_28),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_46])).

tff(c_555,plain,(
    ! [A_118] : r1_tarski(k9_relat_1(k1_xboole_0,A_118),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_541])).

tff(c_564,plain,(
    ! [A_118] : k9_relat_1(k1_xboole_0,A_118) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_555,c_189])).

tff(c_4387,plain,(
    ! [A_118] : k9_relat_1('#skF_4',A_118) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4338,c_4338,c_564])).

tff(c_2440,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_62])).

tff(c_4767,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4387,c_2440])).

tff(c_4771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4402,c_4767])).

tff(c_4772,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2461])).

tff(c_4825,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_4772])).

tff(c_4829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_4825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:04:14 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.12  
% 5.74/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.12  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.74/2.12  
% 5.74/2.12  %Foreground sorts:
% 5.74/2.12  
% 5.74/2.12  
% 5.74/2.12  %Background operators:
% 5.74/2.12  
% 5.74/2.12  
% 5.74/2.12  %Foreground operators:
% 5.74/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.74/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.74/2.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.74/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.74/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.74/2.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.74/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.74/2.12  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.74/2.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.74/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.74/2.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.74/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.74/2.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.74/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.74/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.74/2.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.74/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.74/2.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.74/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.74/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.74/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.74/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.74/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.74/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.12  
% 5.80/2.14  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.80/2.14  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.80/2.14  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.80/2.14  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.80/2.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.80/2.14  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.80/2.14  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.80/2.14  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.80/2.14  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.80/2.14  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.80/2.14  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.80/2.14  tff(f_116, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.80/2.14  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.80/2.14  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.80/2.14  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.80/2.14  tff(c_44, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.80/2.14  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.80/2.14  tff(c_149, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.80/2.14  tff(c_152, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_149])).
% 5.80/2.14  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_152])).
% 5.80/2.14  tff(c_46, plain, (![B_29, A_28]: (r1_tarski(k9_relat_1(B_29, A_28), k2_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.80/2.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.14  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.80/2.14  tff(c_24, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.80/2.14  tff(c_2347, plain, (![A_241, B_242, C_243, D_244]: (k7_relset_1(A_241, B_242, C_243, D_244)=k9_relat_1(C_243, D_244) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.80/2.14  tff(c_2360, plain, (![D_244]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_244)=k9_relat_1('#skF_4', D_244))), inference(resolution, [status(thm)], [c_66, c_2347])).
% 5.80/2.14  tff(c_2423, plain, (![B_254, A_255]: (k1_tarski(k1_funct_1(B_254, A_255))=k2_relat_1(B_254) | k1_tarski(A_255)!=k1_relat_1(B_254) | ~v1_funct_1(B_254) | ~v1_relat_1(B_254))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.80/2.14  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.80/2.14  tff(c_2432, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2423, c_62])).
% 5.80/2.14  tff(c_2438, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_70, c_2432])).
% 5.80/2.14  tff(c_2461, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_2438])).
% 5.80/2.14  tff(c_2462, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2461])).
% 5.80/2.14  tff(c_248, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.80/2.14  tff(c_266, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_248])).
% 5.80/2.14  tff(c_38, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.80/2.14  tff(c_269, plain, (![B_79, A_80]: (k1_tarski(B_79)=A_80 | k1_xboole_0=A_80 | ~r1_tarski(A_80, k1_tarski(B_79)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.80/2.14  tff(c_3932, plain, (![B_359, B_360]: (k1_tarski(B_359)=k1_relat_1(B_360) | k1_relat_1(B_360)=k1_xboole_0 | ~v4_relat_1(B_360, k1_tarski(B_359)) | ~v1_relat_1(B_360))), inference(resolution, [status(thm)], [c_38, c_269])).
% 5.80/2.14  tff(c_3970, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_266, c_3932])).
% 5.80/2.14  tff(c_3987, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_161, c_3970])).
% 5.80/2.14  tff(c_3988, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2462, c_3987])).
% 5.80/2.14  tff(c_56, plain, (![B_40, A_39]: (m1_subset_1(B_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_40), A_39))) | ~r1_tarski(k2_relat_1(B_40), A_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.80/2.14  tff(c_4026, plain, (![A_39]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_39))) | ~r1_tarski(k2_relat_1('#skF_4'), A_39) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3988, c_56])).
% 5.80/2.14  tff(c_4062, plain, (![A_39]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_4'), A_39))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_70, c_24, c_4026])).
% 5.80/2.14  tff(c_4147, plain, (![A_368]: (~r1_tarski(k2_relat_1('#skF_4'), A_368))), inference(splitLeft, [status(thm)], [c_4062])).
% 5.80/2.14  tff(c_4159, plain, $false, inference(resolution, [status(thm)], [c_6, c_4147])).
% 5.80/2.14  tff(c_4160, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_4062])).
% 5.80/2.14  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.80/2.14  tff(c_4186, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4160, c_28])).
% 5.80/2.14  tff(c_26, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.80/2.14  tff(c_113, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.80/2.14  tff(c_117, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_26, c_113])).
% 5.80/2.14  tff(c_181, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.14  tff(c_189, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_117, c_181])).
% 5.80/2.14  tff(c_4338, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4186, c_189])).
% 5.80/2.14  tff(c_4402, plain, (![A_13]: (r1_tarski('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_4338, c_117])).
% 5.80/2.14  tff(c_22, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.80/2.14  tff(c_97, plain, (![A_45, B_46]: (v1_relat_1(k2_zfmisc_1(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.80/2.14  tff(c_99, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_97])).
% 5.80/2.14  tff(c_30, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.80/2.14  tff(c_314, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.80/2.14  tff(c_407, plain, (![A_101, B_102, A_103]: (v5_relat_1(A_101, B_102) | ~r1_tarski(A_101, k2_zfmisc_1(A_103, B_102)))), inference(resolution, [status(thm)], [c_30, c_314])).
% 5.80/2.14  tff(c_439, plain, (![A_103, B_102]: (v5_relat_1(k2_zfmisc_1(A_103, B_102), B_102))), inference(resolution, [status(thm)], [c_6, c_407])).
% 5.80/2.14  tff(c_385, plain, (![B_99, A_100]: (r1_tarski(k2_relat_1(B_99), A_100) | ~v5_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.80/2.14  tff(c_509, plain, (![B_116]: (k2_relat_1(B_116)=k1_xboole_0 | ~v5_relat_1(B_116, k1_xboole_0) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_385, c_189])).
% 5.80/2.14  tff(c_513, plain, (![A_103]: (k2_relat_1(k2_zfmisc_1(A_103, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_103, k1_xboole_0)))), inference(resolution, [status(thm)], [c_439, c_509])).
% 5.80/2.14  tff(c_524, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_99, c_22, c_22, c_513])).
% 5.80/2.14  tff(c_541, plain, (![A_28]: (r1_tarski(k9_relat_1(k1_xboole_0, A_28), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_524, c_46])).
% 5.80/2.14  tff(c_555, plain, (![A_118]: (r1_tarski(k9_relat_1(k1_xboole_0, A_118), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_541])).
% 5.80/2.14  tff(c_564, plain, (![A_118]: (k9_relat_1(k1_xboole_0, A_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_555, c_189])).
% 5.80/2.14  tff(c_4387, plain, (![A_118]: (k9_relat_1('#skF_4', A_118)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4338, c_4338, c_564])).
% 5.80/2.14  tff(c_2440, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_62])).
% 5.80/2.14  tff(c_4767, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4387, c_2440])).
% 5.80/2.14  tff(c_4771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4402, c_4767])).
% 5.80/2.14  tff(c_4772, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2461])).
% 5.80/2.14  tff(c_4825, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_4772])).
% 5.80/2.14  tff(c_4829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_4825])).
% 5.80/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.14  
% 5.80/2.14  Inference rules
% 5.80/2.14  ----------------------
% 5.80/2.14  #Ref     : 0
% 5.80/2.14  #Sup     : 963
% 5.80/2.14  #Fact    : 0
% 5.80/2.14  #Define  : 0
% 5.80/2.14  #Split   : 14
% 5.80/2.14  #Chain   : 0
% 5.80/2.14  #Close   : 0
% 5.80/2.14  
% 5.80/2.14  Ordering : KBO
% 5.80/2.14  
% 5.80/2.14  Simplification rules
% 5.80/2.14  ----------------------
% 5.80/2.14  #Subsume      : 218
% 5.80/2.14  #Demod        : 1341
% 5.80/2.14  #Tautology    : 425
% 5.80/2.14  #SimpNegUnit  : 44
% 5.80/2.14  #BackRed      : 155
% 5.80/2.14  
% 5.80/2.14  #Partial instantiations: 0
% 5.80/2.14  #Strategies tried      : 1
% 5.80/2.14  
% 5.80/2.14  Timing (in seconds)
% 5.80/2.14  ----------------------
% 5.80/2.14  Preprocessing        : 0.37
% 5.80/2.14  Parsing              : 0.20
% 5.80/2.14  CNF conversion       : 0.03
% 5.80/2.14  Main loop            : 0.96
% 5.80/2.14  Inferencing          : 0.30
% 5.80/2.14  Reduction            : 0.36
% 5.80/2.14  Demodulation         : 0.25
% 5.80/2.14  BG Simplification    : 0.04
% 5.80/2.14  Subsumption          : 0.19
% 5.80/2.14  Abstraction          : 0.04
% 5.80/2.14  MUC search           : 0.00
% 5.80/2.14  Cooper               : 0.00
% 5.80/2.14  Total                : 1.37
% 5.80/2.14  Index Insertion      : 0.00
% 5.80/2.14  Index Deletion       : 0.00
% 5.80/2.14  Index Matching       : 0.00
% 5.80/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
