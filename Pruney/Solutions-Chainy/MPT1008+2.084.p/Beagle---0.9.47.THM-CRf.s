%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:37 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 361 expanded)
%              Number of leaves         :   40 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :  202 ( 798 expanded)
%              Number of equality atoms :  102 ( 359 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_189,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_198,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_189])).

tff(c_44,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_205,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_198,c_44])).

tff(c_207,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_589,plain,(
    ! [B_158,A_159] :
      ( k1_tarski(k1_funct_1(B_158,A_159)) = k2_relat_1(B_158)
      | k1_tarski(A_159) != k1_relat_1(B_158)
      | ~ v1_funct_1(B_158)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_462,plain,(
    ! [A_141,B_142,C_143] :
      ( k2_relset_1(A_141,B_142,C_143) = k2_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_471,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_462])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_504,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_60])).

tff(c_595,plain,
    ( k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_504])).

tff(c_635,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_68,c_595])).

tff(c_418,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_427,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_418])).

tff(c_472,plain,(
    ! [A_144,B_145,C_146] :
      ( m1_subset_1(k1_relset_1(A_144,B_145,C_146),k1_zfmisc_1(A_144))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_493,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(k1_tarski('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_472])).

tff(c_499,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_493])).

tff(c_34,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_503,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_499,c_34])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_710,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( k1_enumset1(A_183,B_184,C_185) = D_186
      | k2_tarski(A_183,C_185) = D_186
      | k2_tarski(B_184,C_185) = D_186
      | k2_tarski(A_183,B_184) = D_186
      | k1_tarski(C_185) = D_186
      | k1_tarski(B_184) = D_186
      | k1_tarski(A_183) = D_186
      | k1_xboole_0 = D_186
      | ~ r1_tarski(D_186,k1_enumset1(A_183,B_184,C_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_743,plain,(
    ! [A_3,B_4,D_186] :
      ( k1_enumset1(A_3,A_3,B_4) = D_186
      | k2_tarski(A_3,B_4) = D_186
      | k2_tarski(A_3,B_4) = D_186
      | k2_tarski(A_3,A_3) = D_186
      | k1_tarski(B_4) = D_186
      | k1_tarski(A_3) = D_186
      | k1_tarski(A_3) = D_186
      | k1_xboole_0 = D_186
      | ~ r1_tarski(D_186,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_710])).

tff(c_1266,plain,(
    ! [A_309,B_310,D_311] :
      ( k2_tarski(A_309,B_310) = D_311
      | k2_tarski(A_309,B_310) = D_311
      | k2_tarski(A_309,B_310) = D_311
      | k1_tarski(A_309) = D_311
      | k1_tarski(B_310) = D_311
      | k1_tarski(A_309) = D_311
      | k1_tarski(A_309) = D_311
      | k1_xboole_0 = D_311
      | ~ r1_tarski(D_311,k2_tarski(A_309,B_310)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_743])).

tff(c_1300,plain,(
    ! [A_2,D_311] :
      ( k2_tarski(A_2,A_2) = D_311
      | k2_tarski(A_2,A_2) = D_311
      | k2_tarski(A_2,A_2) = D_311
      | k1_tarski(A_2) = D_311
      | k1_tarski(A_2) = D_311
      | k1_tarski(A_2) = D_311
      | k1_tarski(A_2) = D_311
      | k1_xboole_0 = D_311
      | ~ r1_tarski(D_311,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1266])).

tff(c_1729,plain,(
    ! [A_372,D_373] :
      ( k1_tarski(A_372) = D_373
      | k1_tarski(A_372) = D_373
      | k1_tarski(A_372) = D_373
      | k1_tarski(A_372) = D_373
      | k1_tarski(A_372) = D_373
      | k1_tarski(A_372) = D_373
      | k1_tarski(A_372) = D_373
      | k1_xboole_0 = D_373
      | ~ r1_tarski(D_373,k1_tarski(A_372)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_1300])).

tff(c_1752,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_3')
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_503,c_1729])).

tff(c_1774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_635,c_635,c_635,c_635,c_635,c_635,c_635,c_1752])).

tff(c_1775,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1780,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_2])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1782,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_133,plain,(
    ! [B_64,C_65,A_66] : r1_tarski(k2_tarski(B_64,C_65),k1_enumset1(A_66,B_64,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,(
    ! [A_3,B_4] : r1_tarski(k2_tarski(A_3,B_4),k2_tarski(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_133])).

tff(c_159,plain,(
    ! [A_72,C_73,B_74] :
      ( r2_hidden(A_72,C_73)
      | ~ r1_tarski(k2_tarski(A_72,B_74),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_175,plain,(
    ! [A_75,B_76] : r2_hidden(A_75,k2_tarski(A_75,B_76)) ),
    inference(resolution,[status(thm)],[c_136,c_159])).

tff(c_181,plain,(
    ! [A_2] : r2_hidden(A_2,k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_175])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1779,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_1775,c_40])).

tff(c_1991,plain,(
    ! [A_423,B_424,C_425] :
      ( k1_relset_1(A_423,B_424,C_425) = k1_relat_1(C_425)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(A_423,B_424))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2038,plain,(
    ! [A_434,B_435,A_436] :
      ( k1_relset_1(A_434,B_435,A_436) = k1_relat_1(A_436)
      | ~ r1_tarski(A_436,k2_zfmisc_1(A_434,B_435)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1991])).

tff(c_2050,plain,(
    ! [A_434,B_435] : k1_relset_1(A_434,B_435,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1780,c_2038])).

tff(c_2054,plain,(
    ! [A_434,B_435] : k1_relset_1(A_434,B_435,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_2050])).

tff(c_2080,plain,(
    ! [A_442,B_443,C_444] :
      ( m1_subset_1(k1_relset_1(A_442,B_443,C_444),k1_zfmisc_1(A_442))
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2111,plain,(
    ! [A_447,B_448] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(A_447))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_447,B_448))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2054,c_2080])).

tff(c_2114,plain,(
    ! [A_447,B_448] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(A_447))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(A_447,B_448)) ) ),
    inference(resolution,[status(thm)],[c_36,c_2111])).

tff(c_2120,plain,(
    ! [A_447] : m1_subset_1('#skF_3',k1_zfmisc_1(A_447)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_2114])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1781,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_1775,c_38])).

tff(c_2022,plain,(
    ! [A_431,B_432,C_433] :
      ( k2_relset_1(A_431,B_432,C_433) = k2_relat_1(C_433)
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_zfmisc_1(A_431,B_432))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2063,plain,(
    ! [A_439,B_440,A_441] :
      ( k2_relset_1(A_439,B_440,A_441) = k2_relat_1(A_441)
      | ~ r1_tarski(A_441,k2_zfmisc_1(A_439,B_440)) ) ),
    inference(resolution,[status(thm)],[c_36,c_2022])).

tff(c_2075,plain,(
    ! [A_439,B_440] : k2_relset_1(A_439,B_440,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1780,c_2063])).

tff(c_2079,plain,(
    ! [A_439,B_440] : k2_relset_1(A_439,B_440,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_2075])).

tff(c_58,plain,(
    ! [D_37,C_36,A_34,B_35] :
      ( r2_hidden(k1_funct_1(D_37,C_36),k2_relset_1(A_34,B_35,D_37))
      | k1_xboole_0 = B_35
      | ~ r2_hidden(C_36,A_34)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(D_37,A_34,B_35)
      | ~ v1_funct_1(D_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2235,plain,(
    ! [D_464,C_465,A_466,B_467] :
      ( r2_hidden(k1_funct_1(D_464,C_465),k2_relset_1(A_466,B_467,D_464))
      | B_467 = '#skF_3'
      | ~ r2_hidden(C_465,A_466)
      | ~ m1_subset_1(D_464,k1_zfmisc_1(k2_zfmisc_1(A_466,B_467)))
      | ~ v1_funct_2(D_464,A_466,B_467)
      | ~ v1_funct_1(D_464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_58])).

tff(c_2241,plain,(
    ! [C_465,B_440,A_439] :
      ( r2_hidden(k1_funct_1('#skF_3',C_465),'#skF_3')
      | B_440 = '#skF_3'
      | ~ r2_hidden(C_465,A_439)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_439,B_440)))
      | ~ v1_funct_2('#skF_3',A_439,B_440)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2079,c_2235])).

tff(c_2352,plain,(
    ! [C_486,B_487,A_488] :
      ( r2_hidden(k1_funct_1('#skF_3',C_486),'#skF_3')
      | B_487 = '#skF_3'
      | ~ r2_hidden(C_486,A_488)
      | ~ v1_funct_2('#skF_3',A_488,B_487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2120,c_2241])).

tff(c_2394,plain,(
    ! [A_493,B_494] :
      ( r2_hidden(k1_funct_1('#skF_3',A_493),'#skF_3')
      | B_494 = '#skF_3'
      | ~ v1_funct_2('#skF_3',k1_tarski(A_493),B_494) ) ),
    inference(resolution,[status(thm)],[c_181,c_2352])).

tff(c_2400,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_2394])).

tff(c_2403,plain,(
    r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1782,c_2400])).

tff(c_48,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2408,plain,(
    ~ r1_tarski('#skF_3',k1_funct_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2403,c_48])).

tff(c_2413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_2408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:12:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.94  
% 5.01/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.95  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.01/1.95  
% 5.01/1.95  %Foreground sorts:
% 5.01/1.95  
% 5.01/1.95  
% 5.01/1.95  %Background operators:
% 5.01/1.95  
% 5.01/1.95  
% 5.01/1.95  %Foreground operators:
% 5.01/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.01/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.01/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.01/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.01/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.01/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.01/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.01/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.01/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.01/1.95  tff('#skF_1', type, '#skF_1': $i).
% 5.01/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.01/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.01/1.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.01/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.01/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.01/1.95  
% 5.01/1.96  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 5.01/1.96  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.01/1.96  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.01/1.96  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 5.01/1.96  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.01/1.96  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.01/1.96  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.01/1.96  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.01/1.96  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.01/1.96  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.01/1.96  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 5.01/1.96  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.01/1.96  tff(f_66, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.01/1.96  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.01/1.96  tff(f_122, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 5.01/1.96  tff(f_94, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.01/1.96  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.01/1.96  tff(c_189, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.01/1.96  tff(c_198, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_189])).
% 5.01/1.96  tff(c_44, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.01/1.96  tff(c_205, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_198, c_44])).
% 5.01/1.96  tff(c_207, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_205])).
% 5.01/1.96  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.01/1.96  tff(c_589, plain, (![B_158, A_159]: (k1_tarski(k1_funct_1(B_158, A_159))=k2_relat_1(B_158) | k1_tarski(A_159)!=k1_relat_1(B_158) | ~v1_funct_1(B_158) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.01/1.96  tff(c_462, plain, (![A_141, B_142, C_143]: (k2_relset_1(A_141, B_142, C_143)=k2_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.01/1.96  tff(c_471, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_462])).
% 5.01/1.96  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.01/1.96  tff(c_504, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_60])).
% 5.01/1.96  tff(c_595, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_589, c_504])).
% 5.01/1.96  tff(c_635, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_68, c_595])).
% 5.01/1.96  tff(c_418, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.01/1.96  tff(c_427, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_418])).
% 5.01/1.96  tff(c_472, plain, (![A_144, B_145, C_146]: (m1_subset_1(k1_relset_1(A_144, B_145, C_146), k1_zfmisc_1(A_144)) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.01/1.96  tff(c_493, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(k1_tarski('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_427, c_472])).
% 5.01/1.96  tff(c_499, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_493])).
% 5.01/1.96  tff(c_34, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.01/1.96  tff(c_503, plain, (r1_tarski(k1_relat_1('#skF_3'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_499, c_34])).
% 5.01/1.96  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.01/1.96  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.01/1.96  tff(c_710, plain, (![A_183, B_184, C_185, D_186]: (k1_enumset1(A_183, B_184, C_185)=D_186 | k2_tarski(A_183, C_185)=D_186 | k2_tarski(B_184, C_185)=D_186 | k2_tarski(A_183, B_184)=D_186 | k1_tarski(C_185)=D_186 | k1_tarski(B_184)=D_186 | k1_tarski(A_183)=D_186 | k1_xboole_0=D_186 | ~r1_tarski(D_186, k1_enumset1(A_183, B_184, C_185)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.01/1.96  tff(c_743, plain, (![A_3, B_4, D_186]: (k1_enumset1(A_3, A_3, B_4)=D_186 | k2_tarski(A_3, B_4)=D_186 | k2_tarski(A_3, B_4)=D_186 | k2_tarski(A_3, A_3)=D_186 | k1_tarski(B_4)=D_186 | k1_tarski(A_3)=D_186 | k1_tarski(A_3)=D_186 | k1_xboole_0=D_186 | ~r1_tarski(D_186, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_710])).
% 5.01/1.96  tff(c_1266, plain, (![A_309, B_310, D_311]: (k2_tarski(A_309, B_310)=D_311 | k2_tarski(A_309, B_310)=D_311 | k2_tarski(A_309, B_310)=D_311 | k1_tarski(A_309)=D_311 | k1_tarski(B_310)=D_311 | k1_tarski(A_309)=D_311 | k1_tarski(A_309)=D_311 | k1_xboole_0=D_311 | ~r1_tarski(D_311, k2_tarski(A_309, B_310)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_743])).
% 5.01/1.96  tff(c_1300, plain, (![A_2, D_311]: (k2_tarski(A_2, A_2)=D_311 | k2_tarski(A_2, A_2)=D_311 | k2_tarski(A_2, A_2)=D_311 | k1_tarski(A_2)=D_311 | k1_tarski(A_2)=D_311 | k1_tarski(A_2)=D_311 | k1_tarski(A_2)=D_311 | k1_xboole_0=D_311 | ~r1_tarski(D_311, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1266])).
% 5.01/1.96  tff(c_1729, plain, (![A_372, D_373]: (k1_tarski(A_372)=D_373 | k1_tarski(A_372)=D_373 | k1_tarski(A_372)=D_373 | k1_tarski(A_372)=D_373 | k1_tarski(A_372)=D_373 | k1_tarski(A_372)=D_373 | k1_tarski(A_372)=D_373 | k1_xboole_0=D_373 | ~r1_tarski(D_373, k1_tarski(A_372)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_1300])).
% 5.01/1.96  tff(c_1752, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3') | k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_503, c_1729])).
% 5.01/1.96  tff(c_1774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_635, c_635, c_635, c_635, c_635, c_635, c_635, c_1752])).
% 5.01/1.96  tff(c_1775, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_205])).
% 5.01/1.96  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.01/1.96  tff(c_1780, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_2])).
% 5.01/1.96  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.01/1.96  tff(c_1782, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_62])).
% 5.01/1.96  tff(c_66, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.01/1.96  tff(c_133, plain, (![B_64, C_65, A_66]: (r1_tarski(k2_tarski(B_64, C_65), k1_enumset1(A_66, B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.01/1.96  tff(c_136, plain, (![A_3, B_4]: (r1_tarski(k2_tarski(A_3, B_4), k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_133])).
% 5.01/1.96  tff(c_159, plain, (![A_72, C_73, B_74]: (r2_hidden(A_72, C_73) | ~r1_tarski(k2_tarski(A_72, B_74), C_73))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.01/1.96  tff(c_175, plain, (![A_75, B_76]: (r2_hidden(A_75, k2_tarski(A_75, B_76)))), inference(resolution, [status(thm)], [c_136, c_159])).
% 5.01/1.96  tff(c_181, plain, (![A_2]: (r2_hidden(A_2, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_175])).
% 5.01/1.96  tff(c_36, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.01/1.96  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.01/1.96  tff(c_1779, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_1775, c_40])).
% 5.01/1.96  tff(c_1991, plain, (![A_423, B_424, C_425]: (k1_relset_1(A_423, B_424, C_425)=k1_relat_1(C_425) | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(A_423, B_424))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.01/1.96  tff(c_2038, plain, (![A_434, B_435, A_436]: (k1_relset_1(A_434, B_435, A_436)=k1_relat_1(A_436) | ~r1_tarski(A_436, k2_zfmisc_1(A_434, B_435)))), inference(resolution, [status(thm)], [c_36, c_1991])).
% 5.01/1.96  tff(c_2050, plain, (![A_434, B_435]: (k1_relset_1(A_434, B_435, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1780, c_2038])).
% 5.01/1.96  tff(c_2054, plain, (![A_434, B_435]: (k1_relset_1(A_434, B_435, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_2050])).
% 5.01/1.96  tff(c_2080, plain, (![A_442, B_443, C_444]: (m1_subset_1(k1_relset_1(A_442, B_443, C_444), k1_zfmisc_1(A_442)) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.01/1.96  tff(c_2111, plain, (![A_447, B_448]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_447)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))))), inference(superposition, [status(thm), theory('equality')], [c_2054, c_2080])).
% 5.01/1.96  tff(c_2114, plain, (![A_447, B_448]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_447)) | ~r1_tarski('#skF_3', k2_zfmisc_1(A_447, B_448)))), inference(resolution, [status(thm)], [c_36, c_2111])).
% 5.01/1.96  tff(c_2120, plain, (![A_447]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_447)))), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_2114])).
% 5.01/1.96  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.01/1.96  tff(c_1781, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_1775, c_38])).
% 5.01/1.96  tff(c_2022, plain, (![A_431, B_432, C_433]: (k2_relset_1(A_431, B_432, C_433)=k2_relat_1(C_433) | ~m1_subset_1(C_433, k1_zfmisc_1(k2_zfmisc_1(A_431, B_432))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.01/1.96  tff(c_2063, plain, (![A_439, B_440, A_441]: (k2_relset_1(A_439, B_440, A_441)=k2_relat_1(A_441) | ~r1_tarski(A_441, k2_zfmisc_1(A_439, B_440)))), inference(resolution, [status(thm)], [c_36, c_2022])).
% 5.01/1.96  tff(c_2075, plain, (![A_439, B_440]: (k2_relset_1(A_439, B_440, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1780, c_2063])).
% 5.01/1.97  tff(c_2079, plain, (![A_439, B_440]: (k2_relset_1(A_439, B_440, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_2075])).
% 5.01/1.97  tff(c_58, plain, (![D_37, C_36, A_34, B_35]: (r2_hidden(k1_funct_1(D_37, C_36), k2_relset_1(A_34, B_35, D_37)) | k1_xboole_0=B_35 | ~r2_hidden(C_36, A_34) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_2(D_37, A_34, B_35) | ~v1_funct_1(D_37))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.01/1.97  tff(c_2235, plain, (![D_464, C_465, A_466, B_467]: (r2_hidden(k1_funct_1(D_464, C_465), k2_relset_1(A_466, B_467, D_464)) | B_467='#skF_3' | ~r2_hidden(C_465, A_466) | ~m1_subset_1(D_464, k1_zfmisc_1(k2_zfmisc_1(A_466, B_467))) | ~v1_funct_2(D_464, A_466, B_467) | ~v1_funct_1(D_464))), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_58])).
% 5.01/1.97  tff(c_2241, plain, (![C_465, B_440, A_439]: (r2_hidden(k1_funct_1('#skF_3', C_465), '#skF_3') | B_440='#skF_3' | ~r2_hidden(C_465, A_439) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))) | ~v1_funct_2('#skF_3', A_439, B_440) | ~v1_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2079, c_2235])).
% 5.01/1.97  tff(c_2352, plain, (![C_486, B_487, A_488]: (r2_hidden(k1_funct_1('#skF_3', C_486), '#skF_3') | B_487='#skF_3' | ~r2_hidden(C_486, A_488) | ~v1_funct_2('#skF_3', A_488, B_487))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2120, c_2241])).
% 5.01/1.97  tff(c_2394, plain, (![A_493, B_494]: (r2_hidden(k1_funct_1('#skF_3', A_493), '#skF_3') | B_494='#skF_3' | ~v1_funct_2('#skF_3', k1_tarski(A_493), B_494))), inference(resolution, [status(thm)], [c_181, c_2352])).
% 5.01/1.97  tff(c_2400, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_66, c_2394])).
% 5.01/1.97  tff(c_2403, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1782, c_2400])).
% 5.01/1.97  tff(c_48, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.01/1.97  tff(c_2408, plain, (~r1_tarski('#skF_3', k1_funct_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_2403, c_48])).
% 5.01/1.97  tff(c_2413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1780, c_2408])).
% 5.01/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.97  
% 5.01/1.97  Inference rules
% 5.01/1.97  ----------------------
% 5.01/1.97  #Ref     : 0
% 5.01/1.97  #Sup     : 534
% 5.01/1.97  #Fact    : 1
% 5.01/1.97  #Define  : 0
% 5.01/1.97  #Split   : 4
% 5.01/1.97  #Chain   : 0
% 5.01/1.97  #Close   : 0
% 5.01/1.97  
% 5.01/1.97  Ordering : KBO
% 5.01/1.97  
% 5.01/1.97  Simplification rules
% 5.01/1.97  ----------------------
% 5.01/1.97  #Subsume      : 114
% 5.01/1.97  #Demod        : 253
% 5.01/1.97  #Tautology    : 157
% 5.01/1.97  #SimpNegUnit  : 4
% 5.01/1.97  #BackRed      : 8
% 5.01/1.97  
% 5.01/1.97  #Partial instantiations: 0
% 5.01/1.97  #Strategies tried      : 1
% 5.01/1.97  
% 5.01/1.97  Timing (in seconds)
% 5.01/1.97  ----------------------
% 5.01/1.97  Preprocessing        : 0.34
% 5.01/1.97  Parsing              : 0.18
% 5.01/1.97  CNF conversion       : 0.02
% 5.01/1.97  Main loop            : 0.85
% 5.01/1.97  Inferencing          : 0.30
% 5.01/1.97  Reduction            : 0.25
% 5.01/1.97  Demodulation         : 0.18
% 5.01/1.97  BG Simplification    : 0.04
% 5.01/1.97  Subsumption          : 0.20
% 5.01/1.97  Abstraction          : 0.04
% 5.01/1.97  MUC search           : 0.00
% 5.01/1.97  Cooper               : 0.00
% 5.01/1.97  Total                : 1.24
% 5.01/1.97  Index Insertion      : 0.00
% 5.01/1.97  Index Deletion       : 0.00
% 5.01/1.97  Index Matching       : 0.00
% 5.01/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
