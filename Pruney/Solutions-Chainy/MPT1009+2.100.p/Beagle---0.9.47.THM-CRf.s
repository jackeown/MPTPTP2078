%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:56 EST 2020

% Result     : Theorem 5.39s
% Output     : CNFRefutation 5.39s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 324 expanded)
%              Number of leaves         :   39 ( 127 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 ( 730 expanded)
%              Number of equality atoms :   91 ( 260 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_152,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_152])).

tff(c_32,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k9_relat_1(B_15,A_14),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_177,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_161,c_38])).

tff(c_179,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_310,plain,(
    ! [B_97,A_98] :
      ( k1_tarski(k1_funct_1(B_97,A_98)) = k2_relat_1(B_97)
      | k1_tarski(A_98) != k1_relat_1(B_97)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_337,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_50])).

tff(c_343,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_58,c_337])).

tff(c_358,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_220,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_229,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_220])).

tff(c_252,plain,(
    ! [A_91,B_92,C_93] :
      ( m1_subset_1(k1_relset_1(A_91,B_92,C_93),k1_zfmisc_1(A_91))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_269,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_252])).

tff(c_274,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_269])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_278,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_274,c_28])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2444,plain,(
    ! [A_272,B_273,C_274,D_275] :
      ( k1_enumset1(A_272,B_273,C_274) = D_275
      | k2_tarski(A_272,C_274) = D_275
      | k2_tarski(B_273,C_274) = D_275
      | k2_tarski(A_272,B_273) = D_275
      | k1_tarski(C_274) = D_275
      | k1_tarski(B_273) = D_275
      | k1_tarski(A_272) = D_275
      | k1_xboole_0 = D_275
      | ~ r1_tarski(D_275,k1_enumset1(A_272,B_273,C_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2468,plain,(
    ! [A_3,B_4,D_275] :
      ( k1_enumset1(A_3,A_3,B_4) = D_275
      | k2_tarski(A_3,B_4) = D_275
      | k2_tarski(A_3,B_4) = D_275
      | k2_tarski(A_3,A_3) = D_275
      | k1_tarski(B_4) = D_275
      | k1_tarski(A_3) = D_275
      | k1_tarski(A_3) = D_275
      | k1_xboole_0 = D_275
      | ~ r1_tarski(D_275,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2444])).

tff(c_2758,plain,(
    ! [A_351,B_352,D_353] :
      ( k2_tarski(A_351,B_352) = D_353
      | k2_tarski(A_351,B_352) = D_353
      | k2_tarski(A_351,B_352) = D_353
      | k1_tarski(A_351) = D_353
      | k1_tarski(B_352) = D_353
      | k1_tarski(A_351) = D_353
      | k1_tarski(A_351) = D_353
      | k1_xboole_0 = D_353
      | ~ r1_tarski(D_353,k2_tarski(A_351,B_352)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_2468])).

tff(c_2784,plain,(
    ! [A_2,D_353] :
      ( k2_tarski(A_2,A_2) = D_353
      | k2_tarski(A_2,A_2) = D_353
      | k2_tarski(A_2,A_2) = D_353
      | k1_tarski(A_2) = D_353
      | k1_tarski(A_2) = D_353
      | k1_tarski(A_2) = D_353
      | k1_tarski(A_2) = D_353
      | k1_xboole_0 = D_353
      | ~ r1_tarski(D_353,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2758])).

tff(c_2802,plain,(
    ! [A_354,D_355] :
      ( k1_tarski(A_354) = D_355
      | k1_tarski(A_354) = D_355
      | k1_tarski(A_354) = D_355
      | k1_tarski(A_354) = D_355
      | k1_tarski(A_354) = D_355
      | k1_tarski(A_354) = D_355
      | k1_tarski(A_354) = D_355
      | k1_xboole_0 = D_355
      | ~ r1_tarski(D_355,k1_tarski(A_354)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_2784])).

tff(c_2819,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_278,c_2802])).

tff(c_2833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_358,c_358,c_358,c_358,c_358,c_358,c_358,c_2819])).

tff(c_2835,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_2836,plain,(
    ! [A_356,B_357,C_358,D_359] :
      ( k7_relset_1(A_356,B_357,C_358,D_359) = k9_relat_1(C_358,D_359)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2851,plain,(
    ! [D_359] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_359) = k9_relat_1('#skF_4',D_359) ),
    inference(resolution,[status(thm)],[c_54,c_2836])).

tff(c_2991,plain,(
    ! [D_359] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_359) = k9_relat_1('#skF_4',D_359) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2835,c_2851])).

tff(c_2834,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_3039,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2991,c_2835,c_2834])).

tff(c_3042,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3039])).

tff(c_3046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3042])).

tff(c_3047,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3052,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_2])).

tff(c_34,plain,(
    ! [A_16] : k9_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3051,plain,(
    ! [A_16] : k9_relat_1('#skF_4',A_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_3047,c_34])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3048,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_3058,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_3048])).

tff(c_3117,plain,(
    ! [A_386,B_387,C_388] :
      ( k1_relset_1(A_386,B_387,C_388) = k1_relat_1(C_388)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3157,plain,(
    ! [A_392,B_393,A_394] :
      ( k1_relset_1(A_392,B_393,A_394) = k1_relat_1(A_394)
      | ~ r1_tarski(A_394,k2_zfmisc_1(A_392,B_393)) ) ),
    inference(resolution,[status(thm)],[c_30,c_3117])).

tff(c_3161,plain,(
    ! [A_392,B_393] : k1_relset_1(A_392,B_393,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3052,c_3157])).

tff(c_3165,plain,(
    ! [A_395,B_396] : k1_relset_1(A_395,B_396,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_3161])).

tff(c_44,plain,(
    ! [A_23,B_24,C_25] :
      ( m1_subset_1(k1_relset_1(A_23,B_24,C_25),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3175,plain,(
    ! [A_397,B_398] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_397))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_397,B_398))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3165,c_44])).

tff(c_3178,plain,(
    ! [A_397,B_398] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_397))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_397,B_398)) ) ),
    inference(resolution,[status(thm)],[c_30,c_3175])).

tff(c_3184,plain,(
    ! [A_397] : m1_subset_1('#skF_4',k1_zfmisc_1(A_397)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3052,c_3178])).

tff(c_3275,plain,(
    ! [A_408,B_409,C_410,D_411] :
      ( k7_relset_1(A_408,B_409,C_410,D_411) = k9_relat_1(C_410,D_411)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(A_408,B_409))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3278,plain,(
    ! [A_408,B_409,D_411] : k7_relset_1(A_408,B_409,'#skF_4',D_411) = k9_relat_1('#skF_4',D_411) ),
    inference(resolution,[status(thm)],[c_3184,c_3275])).

tff(c_3286,plain,(
    ! [A_408,B_409,D_411] : k7_relset_1(A_408,B_409,'#skF_4',D_411) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3051,c_3278])).

tff(c_3289,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3286,c_50])).

tff(c_3292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3052,c_3289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.39/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.39/2.05  
% 5.39/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.39/2.05  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.39/2.05  
% 5.39/2.05  %Foreground sorts:
% 5.39/2.05  
% 5.39/2.05  
% 5.39/2.05  %Background operators:
% 5.39/2.05  
% 5.39/2.05  
% 5.39/2.05  %Foreground operators:
% 5.39/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.39/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.39/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.39/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.39/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.39/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.39/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.39/2.05  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.39/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.39/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.39/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.39/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.39/2.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.39/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.39/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.39/2.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.39/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.39/2.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.39/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.39/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.39/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.39/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.39/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.39/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.39/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.39/2.05  
% 5.39/2.07  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.39/2.07  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.39/2.07  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.39/2.07  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.39/2.07  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.39/2.07  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.39/2.07  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.39/2.07  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.39/2.07  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.39/2.07  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.39/2.07  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 5.39/2.07  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.39/2.07  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.39/2.07  tff(f_70, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 5.39/2.07  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.39/2.07  tff(c_152, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.39/2.07  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_152])).
% 5.39/2.07  tff(c_32, plain, (![B_15, A_14]: (r1_tarski(k9_relat_1(B_15, A_14), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.39/2.07  tff(c_38, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.39/2.07  tff(c_177, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_161, c_38])).
% 5.39/2.07  tff(c_179, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_177])).
% 5.39/2.07  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.39/2.07  tff(c_310, plain, (![B_97, A_98]: (k1_tarski(k1_funct_1(B_97, A_98))=k2_relat_1(B_97) | k1_tarski(A_98)!=k1_relat_1(B_97) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.39/2.07  tff(c_50, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.39/2.07  tff(c_337, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_310, c_50])).
% 5.39/2.07  tff(c_343, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_58, c_337])).
% 5.39/2.07  tff(c_358, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_343])).
% 5.39/2.07  tff(c_220, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.39/2.07  tff(c_229, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_220])).
% 5.39/2.07  tff(c_252, plain, (![A_91, B_92, C_93]: (m1_subset_1(k1_relset_1(A_91, B_92, C_93), k1_zfmisc_1(A_91)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.39/2.07  tff(c_269, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_229, c_252])).
% 5.39/2.07  tff(c_274, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_269])).
% 5.39/2.07  tff(c_28, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.39/2.07  tff(c_278, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_274, c_28])).
% 5.39/2.07  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.39/2.07  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.39/2.07  tff(c_2444, plain, (![A_272, B_273, C_274, D_275]: (k1_enumset1(A_272, B_273, C_274)=D_275 | k2_tarski(A_272, C_274)=D_275 | k2_tarski(B_273, C_274)=D_275 | k2_tarski(A_272, B_273)=D_275 | k1_tarski(C_274)=D_275 | k1_tarski(B_273)=D_275 | k1_tarski(A_272)=D_275 | k1_xboole_0=D_275 | ~r1_tarski(D_275, k1_enumset1(A_272, B_273, C_274)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.39/2.07  tff(c_2468, plain, (![A_3, B_4, D_275]: (k1_enumset1(A_3, A_3, B_4)=D_275 | k2_tarski(A_3, B_4)=D_275 | k2_tarski(A_3, B_4)=D_275 | k2_tarski(A_3, A_3)=D_275 | k1_tarski(B_4)=D_275 | k1_tarski(A_3)=D_275 | k1_tarski(A_3)=D_275 | k1_xboole_0=D_275 | ~r1_tarski(D_275, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2444])).
% 5.39/2.07  tff(c_2758, plain, (![A_351, B_352, D_353]: (k2_tarski(A_351, B_352)=D_353 | k2_tarski(A_351, B_352)=D_353 | k2_tarski(A_351, B_352)=D_353 | k1_tarski(A_351)=D_353 | k1_tarski(B_352)=D_353 | k1_tarski(A_351)=D_353 | k1_tarski(A_351)=D_353 | k1_xboole_0=D_353 | ~r1_tarski(D_353, k2_tarski(A_351, B_352)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_2468])).
% 5.39/2.07  tff(c_2784, plain, (![A_2, D_353]: (k2_tarski(A_2, A_2)=D_353 | k2_tarski(A_2, A_2)=D_353 | k2_tarski(A_2, A_2)=D_353 | k1_tarski(A_2)=D_353 | k1_tarski(A_2)=D_353 | k1_tarski(A_2)=D_353 | k1_tarski(A_2)=D_353 | k1_xboole_0=D_353 | ~r1_tarski(D_353, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2758])).
% 5.39/2.07  tff(c_2802, plain, (![A_354, D_355]: (k1_tarski(A_354)=D_355 | k1_tarski(A_354)=D_355 | k1_tarski(A_354)=D_355 | k1_tarski(A_354)=D_355 | k1_tarski(A_354)=D_355 | k1_tarski(A_354)=D_355 | k1_tarski(A_354)=D_355 | k1_xboole_0=D_355 | ~r1_tarski(D_355, k1_tarski(A_354)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_2784])).
% 5.39/2.07  tff(c_2819, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_278, c_2802])).
% 5.39/2.07  tff(c_2833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_358, c_358, c_358, c_358, c_358, c_358, c_358, c_2819])).
% 5.39/2.07  tff(c_2835, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_343])).
% 5.39/2.07  tff(c_2836, plain, (![A_356, B_357, C_358, D_359]: (k7_relset_1(A_356, B_357, C_358, D_359)=k9_relat_1(C_358, D_359) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.39/2.07  tff(c_2851, plain, (![D_359]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_359)=k9_relat_1('#skF_4', D_359))), inference(resolution, [status(thm)], [c_54, c_2836])).
% 5.39/2.07  tff(c_2991, plain, (![D_359]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_359)=k9_relat_1('#skF_4', D_359))), inference(demodulation, [status(thm), theory('equality')], [c_2835, c_2851])).
% 5.39/2.07  tff(c_2834, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_343])).
% 5.39/2.07  tff(c_3039, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2991, c_2835, c_2834])).
% 5.39/2.07  tff(c_3042, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3039])).
% 5.39/2.07  tff(c_3046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_3042])).
% 5.39/2.07  tff(c_3047, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_177])).
% 5.39/2.07  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.39/2.07  tff(c_3052, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_2])).
% 5.39/2.07  tff(c_34, plain, (![A_16]: (k9_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.39/2.07  tff(c_3051, plain, (![A_16]: (k9_relat_1('#skF_4', A_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_3047, c_34])).
% 5.39/2.07  tff(c_30, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.39/2.07  tff(c_3048, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_177])).
% 5.39/2.07  tff(c_3058, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_3048])).
% 5.39/2.07  tff(c_3117, plain, (![A_386, B_387, C_388]: (k1_relset_1(A_386, B_387, C_388)=k1_relat_1(C_388) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.39/2.07  tff(c_3157, plain, (![A_392, B_393, A_394]: (k1_relset_1(A_392, B_393, A_394)=k1_relat_1(A_394) | ~r1_tarski(A_394, k2_zfmisc_1(A_392, B_393)))), inference(resolution, [status(thm)], [c_30, c_3117])).
% 5.39/2.07  tff(c_3161, plain, (![A_392, B_393]: (k1_relset_1(A_392, B_393, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3052, c_3157])).
% 5.39/2.07  tff(c_3165, plain, (![A_395, B_396]: (k1_relset_1(A_395, B_396, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_3161])).
% 5.39/2.07  tff(c_44, plain, (![A_23, B_24, C_25]: (m1_subset_1(k1_relset_1(A_23, B_24, C_25), k1_zfmisc_1(A_23)) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.39/2.07  tff(c_3175, plain, (![A_397, B_398]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_397)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_397, B_398))))), inference(superposition, [status(thm), theory('equality')], [c_3165, c_44])).
% 5.39/2.07  tff(c_3178, plain, (![A_397, B_398]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_397)) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_397, B_398)))), inference(resolution, [status(thm)], [c_30, c_3175])).
% 5.39/2.07  tff(c_3184, plain, (![A_397]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_397)))), inference(demodulation, [status(thm), theory('equality')], [c_3052, c_3178])).
% 5.39/2.07  tff(c_3275, plain, (![A_408, B_409, C_410, D_411]: (k7_relset_1(A_408, B_409, C_410, D_411)=k9_relat_1(C_410, D_411) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(A_408, B_409))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.39/2.07  tff(c_3278, plain, (![A_408, B_409, D_411]: (k7_relset_1(A_408, B_409, '#skF_4', D_411)=k9_relat_1('#skF_4', D_411))), inference(resolution, [status(thm)], [c_3184, c_3275])).
% 5.39/2.07  tff(c_3286, plain, (![A_408, B_409, D_411]: (k7_relset_1(A_408, B_409, '#skF_4', D_411)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3051, c_3278])).
% 5.39/2.07  tff(c_3289, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3286, c_50])).
% 5.39/2.07  tff(c_3292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3052, c_3289])).
% 5.39/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.39/2.07  
% 5.39/2.07  Inference rules
% 5.39/2.07  ----------------------
% 5.39/2.07  #Ref     : 0
% 5.39/2.07  #Sup     : 618
% 5.39/2.07  #Fact    : 6
% 5.39/2.07  #Define  : 0
% 5.39/2.07  #Split   : 9
% 5.39/2.07  #Chain   : 0
% 5.39/2.07  #Close   : 0
% 5.39/2.07  
% 5.39/2.07  Ordering : KBO
% 5.39/2.07  
% 5.39/2.07  Simplification rules
% 5.39/2.07  ----------------------
% 5.39/2.07  #Subsume      : 31
% 5.39/2.07  #Demod        : 745
% 5.39/2.07  #Tautology    : 324
% 5.39/2.07  #SimpNegUnit  : 32
% 5.39/2.07  #BackRed      : 105
% 5.39/2.07  
% 5.39/2.07  #Partial instantiations: 0
% 5.39/2.07  #Strategies tried      : 1
% 5.39/2.07  
% 5.39/2.07  Timing (in seconds)
% 5.39/2.07  ----------------------
% 5.39/2.07  Preprocessing        : 0.33
% 5.39/2.07  Parsing              : 0.18
% 5.39/2.07  CNF conversion       : 0.02
% 5.39/2.07  Main loop            : 0.97
% 5.39/2.07  Inferencing          : 0.35
% 5.39/2.07  Reduction            : 0.33
% 5.39/2.07  Demodulation         : 0.24
% 5.79/2.07  BG Simplification    : 0.04
% 5.79/2.07  Subsumption          : 0.16
% 5.79/2.07  Abstraction          : 0.07
% 5.79/2.07  MUC search           : 0.00
% 5.79/2.07  Cooper               : 0.00
% 5.79/2.07  Total                : 1.34
% 5.79/2.07  Index Insertion      : 0.00
% 5.79/2.07  Index Deletion       : 0.00
% 5.79/2.07  Index Matching       : 0.00
% 5.79/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
