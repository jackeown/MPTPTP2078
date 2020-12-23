%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:49 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 282 expanded)
%              Number of leaves         :   41 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 577 expanded)
%              Number of equality atoms :   57 ( 194 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_143,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_151,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,A_13),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_295,plain,(
    ! [B_72,A_73] :
      ( k1_tarski(k1_funct_1(B_72,A_73)) = k2_relat_1(B_72)
      | k1_tarski(A_73) != k1_relat_1(B_72)
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_304,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_46])).

tff(c_316,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_54,c_304])).

tff(c_338,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_34,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_161,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_151,c_34])).

tff(c_174,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_188,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_196,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_188])).

tff(c_273,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k1_relat_1(B_67),A_68)
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k1_tarski(B_6) = A_5
      | k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_tarski(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_320,plain,(
    ! [B_77,B_78] :
      ( k1_tarski(B_77) = k1_relat_1(B_78)
      | k1_relat_1(B_78) = k1_xboole_0
      | ~ v4_relat_1(B_78,k1_tarski(B_77))
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_273,c_8])).

tff(c_326,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_320])).

tff(c_333,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_326])).

tff(c_334,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_333])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_334])).

tff(c_341,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_347,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_50])).

tff(c_44,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( k7_relset_1(A_28,B_29,C_30,D_31) = k9_relat_1(C_30,D_31)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_410,plain,(
    ! [D_31] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_31) = k9_relat_1('#skF_4',D_31) ),
    inference(resolution,[status(thm)],[c_347,c_44])).

tff(c_340,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_437,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_340])).

tff(c_439,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_437])).

tff(c_451,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_439])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_451])).

tff(c_456,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_465,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_28])).

tff(c_32,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_160,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_151,c_32])).

tff(c_162,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_458,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_162])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_458])).

tff(c_495,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_503,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_2])).

tff(c_502,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_495,c_28])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_504,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_495,c_30])).

tff(c_574,plain,(
    ! [B_105,A_106] :
      ( v4_relat_1(B_105,A_106)
      | ~ r1_tarski(k1_relat_1(B_105),A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_577,plain,(
    ! [A_106] :
      ( v4_relat_1('#skF_4',A_106)
      | ~ r1_tarski('#skF_4',A_106)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_574])).

tff(c_586,plain,(
    ! [A_110] : v4_relat_1('#skF_4',A_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_503,c_577])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_589,plain,(
    ! [A_110] :
      ( k7_relat_1('#skF_4',A_110) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_586,c_26])).

tff(c_594,plain,(
    ! [A_111] : k7_relat_1('#skF_4',A_111) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_589])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_599,plain,(
    ! [A_111] :
      ( k9_relat_1('#skF_4',A_111) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_24])).

tff(c_604,plain,(
    ! [A_111] : k9_relat_1('#skF_4',A_111) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_502,c_599])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_501,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_14])).

tff(c_661,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k7_relset_1(A_124,B_125,C_126,D_127) = k9_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_664,plain,(
    ! [A_124,B_125,D_127] : k7_relset_1(A_124,B_125,'#skF_4',D_127) = k9_relat_1('#skF_4',D_127) ),
    inference(resolution,[status(thm)],[c_501,c_661])).

tff(c_666,plain,(
    ! [A_124,B_125,D_127] : k7_relset_1(A_124,B_125,'#skF_4',D_127) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_664])).

tff(c_667,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_46])).

tff(c_670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  
% 2.60/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.89/1.38  
% 2.89/1.38  %Foreground sorts:
% 2.89/1.38  
% 2.89/1.38  
% 2.89/1.38  %Background operators:
% 2.89/1.38  
% 2.89/1.38  
% 2.89/1.38  %Foreground operators:
% 2.89/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.89/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.89/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.89/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.89/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.89/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.89/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.38  
% 2.89/1.40  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 2.89/1.40  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.89/1.40  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.89/1.40  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.89/1.40  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.89/1.40  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.89/1.40  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.89/1.40  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.89/1.40  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.89/1.40  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.89/1.40  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.89/1.40  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.89/1.40  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.89/1.40  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.89/1.40  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.89/1.40  tff(c_143, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.89/1.40  tff(c_151, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_143])).
% 2.89/1.40  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, A_13), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.89/1.40  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.89/1.40  tff(c_295, plain, (![B_72, A_73]: (k1_tarski(k1_funct_1(B_72, A_73))=k2_relat_1(B_72) | k1_tarski(A_73)!=k1_relat_1(B_72) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.89/1.40  tff(c_46, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.89/1.40  tff(c_304, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_295, c_46])).
% 2.89/1.40  tff(c_316, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_54, c_304])).
% 2.89/1.40  tff(c_338, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_316])).
% 2.89/1.40  tff(c_34, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.89/1.40  tff(c_161, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_151, c_34])).
% 2.89/1.40  tff(c_174, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_161])).
% 2.89/1.40  tff(c_188, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.89/1.40  tff(c_196, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_188])).
% 2.89/1.40  tff(c_273, plain, (![B_67, A_68]: (r1_tarski(k1_relat_1(B_67), A_68) | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.40  tff(c_8, plain, (![B_6, A_5]: (k1_tarski(B_6)=A_5 | k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_tarski(B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.40  tff(c_320, plain, (![B_77, B_78]: (k1_tarski(B_77)=k1_relat_1(B_78) | k1_relat_1(B_78)=k1_xboole_0 | ~v4_relat_1(B_78, k1_tarski(B_77)) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_273, c_8])).
% 2.89/1.40  tff(c_326, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_196, c_320])).
% 2.89/1.40  tff(c_333, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_151, c_326])).
% 2.89/1.40  tff(c_334, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_174, c_333])).
% 2.89/1.40  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_334])).
% 2.89/1.40  tff(c_341, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_316])).
% 2.89/1.40  tff(c_347, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_50])).
% 2.89/1.40  tff(c_44, plain, (![A_28, B_29, C_30, D_31]: (k7_relset_1(A_28, B_29, C_30, D_31)=k9_relat_1(C_30, D_31) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.89/1.40  tff(c_410, plain, (![D_31]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_31)=k9_relat_1('#skF_4', D_31))), inference(resolution, [status(thm)], [c_347, c_44])).
% 2.89/1.40  tff(c_340, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_316])).
% 2.89/1.40  tff(c_437, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_340])).
% 2.89/1.40  tff(c_439, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_410, c_437])).
% 2.89/1.40  tff(c_451, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_439])).
% 2.89/1.40  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_451])).
% 2.89/1.40  tff(c_456, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_161])).
% 2.89/1.40  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.89/1.40  tff(c_465, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_28])).
% 2.89/1.40  tff(c_32, plain, (![A_19]: (k2_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.89/1.40  tff(c_160, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_151, c_32])).
% 2.89/1.40  tff(c_162, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_160])).
% 2.89/1.40  tff(c_458, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_162])).
% 2.89/1.40  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_465, c_458])).
% 2.89/1.40  tff(c_495, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_160])).
% 2.89/1.40  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.89/1.40  tff(c_503, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_495, c_2])).
% 2.89/1.40  tff(c_502, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_495, c_28])).
% 2.89/1.40  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.89/1.40  tff(c_504, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_495, c_30])).
% 2.89/1.40  tff(c_574, plain, (![B_105, A_106]: (v4_relat_1(B_105, A_106) | ~r1_tarski(k1_relat_1(B_105), A_106) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.40  tff(c_577, plain, (![A_106]: (v4_relat_1('#skF_4', A_106) | ~r1_tarski('#skF_4', A_106) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_504, c_574])).
% 2.89/1.40  tff(c_586, plain, (![A_110]: (v4_relat_1('#skF_4', A_110))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_503, c_577])).
% 2.89/1.40  tff(c_26, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.40  tff(c_589, plain, (![A_110]: (k7_relat_1('#skF_4', A_110)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_586, c_26])).
% 2.89/1.40  tff(c_594, plain, (![A_111]: (k7_relat_1('#skF_4', A_111)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_589])).
% 2.89/1.40  tff(c_24, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.89/1.40  tff(c_599, plain, (![A_111]: (k9_relat_1('#skF_4', A_111)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_594, c_24])).
% 2.89/1.40  tff(c_604, plain, (![A_111]: (k9_relat_1('#skF_4', A_111)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_502, c_599])).
% 2.89/1.40  tff(c_14, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.40  tff(c_501, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_495, c_14])).
% 2.89/1.40  tff(c_661, plain, (![A_124, B_125, C_126, D_127]: (k7_relset_1(A_124, B_125, C_126, D_127)=k9_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.89/1.40  tff(c_664, plain, (![A_124, B_125, D_127]: (k7_relset_1(A_124, B_125, '#skF_4', D_127)=k9_relat_1('#skF_4', D_127))), inference(resolution, [status(thm)], [c_501, c_661])).
% 2.89/1.40  tff(c_666, plain, (![A_124, B_125, D_127]: (k7_relset_1(A_124, B_125, '#skF_4', D_127)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_664])).
% 2.89/1.40  tff(c_667, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_666, c_46])).
% 2.89/1.40  tff(c_670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_503, c_667])).
% 2.89/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.40  
% 2.89/1.40  Inference rules
% 2.89/1.40  ----------------------
% 2.89/1.40  #Ref     : 0
% 2.89/1.40  #Sup     : 122
% 2.89/1.40  #Fact    : 0
% 2.89/1.40  #Define  : 0
% 2.89/1.40  #Split   : 4
% 2.89/1.40  #Chain   : 0
% 2.89/1.40  #Close   : 0
% 2.89/1.40  
% 2.89/1.40  Ordering : KBO
% 2.89/1.40  
% 2.89/1.40  Simplification rules
% 2.89/1.40  ----------------------
% 2.89/1.40  #Subsume      : 0
% 2.89/1.40  #Demod        : 127
% 2.89/1.40  #Tautology    : 90
% 2.89/1.40  #SimpNegUnit  : 2
% 2.89/1.40  #BackRed      : 31
% 2.89/1.40  
% 2.89/1.40  #Partial instantiations: 0
% 2.89/1.40  #Strategies tried      : 1
% 2.89/1.40  
% 2.89/1.40  Timing (in seconds)
% 2.89/1.40  ----------------------
% 2.89/1.41  Preprocessing        : 0.33
% 2.89/1.41  Parsing              : 0.18
% 2.89/1.41  CNF conversion       : 0.02
% 2.89/1.41  Main loop            : 0.30
% 2.89/1.41  Inferencing          : 0.11
% 2.89/1.41  Reduction            : 0.10
% 2.89/1.41  Demodulation         : 0.08
% 2.89/1.41  BG Simplification    : 0.02
% 2.89/1.41  Subsumption          : 0.05
% 2.89/1.41  Abstraction          : 0.01
% 2.89/1.41  MUC search           : 0.00
% 2.89/1.41  Cooper               : 0.00
% 2.89/1.41  Total                : 0.67
% 2.89/1.41  Index Insertion      : 0.00
% 2.89/1.41  Index Deletion       : 0.00
% 2.89/1.41  Index Matching       : 0.00
% 2.89/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
