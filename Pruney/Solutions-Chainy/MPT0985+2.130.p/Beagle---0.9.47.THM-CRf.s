%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:47 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 403 expanded)
%              Number of leaves         :   42 ( 145 expanded)
%              Depth                    :   10
%              Number of atoms          :  220 (1007 expanded)
%              Number of equality atoms :   99 ( 315 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_172,plain,(
    ! [A_55] :
      ( v1_funct_1(k2_funct_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_154,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_175,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_154])).

tff(c_178,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_175])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_200,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_207,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_200])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_207])).

tff(c_221,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_303,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_262,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_279,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_262])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_353,plain,(
    ! [A_77] :
      ( k4_relat_1(A_77) = k2_funct_1(A_77)
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_356,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_353])).

tff(c_359,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_72,c_356])).

tff(c_437,plain,(
    ! [A_94,B_95,C_96] :
      ( k3_relset_1(A_94,B_95,C_96) = k4_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_444,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_437])).

tff(c_457,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_444])).

tff(c_684,plain,(
    ! [A_126,B_127,C_128] :
      ( m1_subset_1(k3_relset_1(A_126,B_127,C_128),k1_zfmisc_1(k2_zfmisc_1(B_127,A_126)))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_707,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_684])).

tff(c_723,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_707])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_723])).

tff(c_726,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_30,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_288,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_279,c_30])).

tff(c_729,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_912,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_936,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_912])).

tff(c_1004,plain,(
    ! [A_164,B_165,C_166] :
      ( m1_subset_1(k1_relset_1(A_164,B_165,C_166),k1_zfmisc_1(A_164))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1038,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_1004])).

tff(c_1055,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1038])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1083,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1055,c_14])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1087,plain,(
    k2_xboole_0(k1_relat_1('#skF_3'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1083,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | k2_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1091,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_4])).

tff(c_1094,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_729,c_1091])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_954,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_relset_1(A_159,B_160,C_161) = k2_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_964,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_954])).

tff(c_979,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_964])).

tff(c_798,plain,(
    ! [A_134] :
      ( k4_relat_1(A_134) = k2_funct_1(A_134)
      | ~ v2_funct_1(A_134)
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_801,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_798])).

tff(c_804,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_72,c_801])).

tff(c_22,plain,(
    ! [A_13] :
      ( k1_relat_1(k4_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_808,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_22])).

tff(c_815,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_808])).

tff(c_727,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_915,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_727,c_912])).

tff(c_934,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_915])).

tff(c_982,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_934])).

tff(c_1370,plain,(
    ! [B_185,C_186,A_187] :
      ( k1_xboole_0 = B_185
      | v1_funct_2(C_186,A_187,B_185)
      | k1_relset_1(A_187,B_185,C_186) != A_187
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1383,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_727,c_1370])).

tff(c_1408,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_1383])).

tff(c_1410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_726,c_1094,c_1408])).

tff(c_1411,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1425,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1411,c_1411,c_24])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_287,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_279,c_28])).

tff(c_728,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_1413,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1411,c_728])).

tff(c_1457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_1413])).

tff(c_1458,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1472,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1458,c_26])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1468,plain,(
    ! [A_7] : m1_subset_1('#skF_3',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_12])).

tff(c_1837,plain,(
    ! [A_236,B_237,C_238] :
      ( k1_relset_1(A_236,B_237,C_238) = k1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1841,plain,(
    ! [A_236,B_237] : k1_relset_1(A_236,B_237,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1468,c_1837])).

tff(c_1853,plain,(
    ! [A_236,B_237] : k1_relset_1(A_236,B_237,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1472,c_1841])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_76,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_2347,plain,(
    ! [C_303,B_304] :
      ( v1_funct_2(C_303,'#skF_3',B_304)
      | k1_relset_1('#skF_3',B_304,C_303) != '#skF_3'
      | ~ m1_subset_1(C_303,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1458,c_1458,c_1458,c_76])).

tff(c_2355,plain,(
    ! [B_304] :
      ( v1_funct_2('#skF_3','#skF_3',B_304)
      | k1_relset_1('#skF_3',B_304,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1468,c_2347])).

tff(c_2364,plain,(
    ! [B_304] : v1_funct_2('#skF_3','#skF_3',B_304) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1853,c_2355])).

tff(c_1459,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_1486,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1459])).

tff(c_1763,plain,(
    ! [A_221,B_222,C_223] :
      ( k2_relset_1(A_221,B_222,C_223) = k2_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1767,plain,(
    ! [A_221,B_222] : k2_relset_1(A_221,B_222,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1468,c_1763])).

tff(c_1779,plain,(
    ! [A_221,B_222] : k2_relset_1(A_221,B_222,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1767])).

tff(c_1781,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_64])).

tff(c_1538,plain,(
    ! [A_193] :
      ( k4_relat_1(A_193) = k2_funct_1(A_193)
      | ~ v2_funct_1(A_193)
      | ~ v1_funct_1(A_193)
      | ~ v1_relat_1(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1541,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1538])).

tff(c_1544,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_72,c_1541])).

tff(c_20,plain,(
    ! [A_13] :
      ( k2_relat_1(k4_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1551,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1544,c_20])).

tff(c_1557,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_1472,c_1551])).

tff(c_38,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1484,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_727,c_38])).

tff(c_1641,plain,(
    ! [A_209] :
      ( k2_relat_1(A_209) != '#skF_3'
      | A_209 = '#skF_3'
      | ~ v1_relat_1(A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1458,c_28])).

tff(c_1644,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1484,c_1641])).

tff(c_1653,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1644])).

tff(c_1688,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1653,c_726])).

tff(c_1789,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1688])).

tff(c_2368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_1789])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:23:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.76  
% 4.36/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.76  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.36/1.76  
% 4.36/1.76  %Foreground sorts:
% 4.36/1.76  
% 4.36/1.76  
% 4.36/1.76  %Background operators:
% 4.36/1.76  
% 4.36/1.76  
% 4.36/1.76  %Foreground operators:
% 4.36/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.36/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.36/1.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.36/1.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.36/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.36/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.36/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.76  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 4.36/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.36/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.36/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.36/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.36/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.36/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.36/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.36/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.36/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.36/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.36/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.36/1.76  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.36/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.36/1.76  
% 4.50/1.81  tff(f_143, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.50/1.81  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.50/1.81  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.50/1.81  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 4.50/1.81  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 4.50/1.81  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 4.50/1.81  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.50/1.81  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.50/1.81  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.50/1.81  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.50/1.81  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.50/1.81  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 4.50/1.81  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.50/1.81  tff(f_57, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 4.50/1.81  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.50/1.81  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.50/1.81  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.50/1.81  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.50/1.81  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.50/1.81  tff(c_172, plain, (![A_55]: (v1_funct_1(k2_funct_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.50/1.81  tff(c_62, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.50/1.81  tff(c_154, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.50/1.81  tff(c_175, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_172, c_154])).
% 4.50/1.81  tff(c_178, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_175])).
% 4.50/1.81  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.50/1.81  tff(c_200, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.50/1.81  tff(c_207, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_200])).
% 4.50/1.81  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_207])).
% 4.50/1.81  tff(c_221, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 4.50/1.81  tff(c_303, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_221])).
% 4.50/1.81  tff(c_262, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.50/1.81  tff(c_279, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_262])).
% 4.50/1.81  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.50/1.81  tff(c_353, plain, (![A_77]: (k4_relat_1(A_77)=k2_funct_1(A_77) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.50/1.81  tff(c_356, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_353])).
% 4.50/1.81  tff(c_359, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_72, c_356])).
% 4.50/1.81  tff(c_437, plain, (![A_94, B_95, C_96]: (k3_relset_1(A_94, B_95, C_96)=k4_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.50/1.81  tff(c_444, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_437])).
% 4.50/1.81  tff(c_457, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_444])).
% 4.50/1.81  tff(c_684, plain, (![A_126, B_127, C_128]: (m1_subset_1(k3_relset_1(A_126, B_127, C_128), k1_zfmisc_1(k2_zfmisc_1(B_127, A_126))) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.50/1.81  tff(c_707, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_457, c_684])).
% 4.50/1.81  tff(c_723, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_707])).
% 4.50/1.81  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_723])).
% 4.50/1.81  tff(c_726, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_221])).
% 4.50/1.81  tff(c_30, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.50/1.81  tff(c_288, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_279, c_30])).
% 4.50/1.81  tff(c_729, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_288])).
% 4.50/1.81  tff(c_912, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.50/1.81  tff(c_936, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_912])).
% 4.50/1.81  tff(c_1004, plain, (![A_164, B_165, C_166]: (m1_subset_1(k1_relset_1(A_164, B_165, C_166), k1_zfmisc_1(A_164)) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.50/1.81  tff(c_1038, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_936, c_1004])).
% 4.50/1.81  tff(c_1055, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1038])).
% 4.50/1.81  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.50/1.81  tff(c_1083, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1055, c_14])).
% 4.50/1.81  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.81  tff(c_1087, plain, (k2_xboole_0(k1_relat_1('#skF_3'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1083, c_2])).
% 4.50/1.81  tff(c_4, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | k2_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.81  tff(c_1091, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1087, c_4])).
% 4.50/1.81  tff(c_1094, plain, (k1_xboole_0!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_729, c_1091])).
% 4.50/1.81  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.50/1.81  tff(c_954, plain, (![A_159, B_160, C_161]: (k2_relset_1(A_159, B_160, C_161)=k2_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.50/1.81  tff(c_964, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_954])).
% 4.50/1.81  tff(c_979, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_964])).
% 4.50/1.81  tff(c_798, plain, (![A_134]: (k4_relat_1(A_134)=k2_funct_1(A_134) | ~v2_funct_1(A_134) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.50/1.81  tff(c_801, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_798])).
% 4.50/1.81  tff(c_804, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_72, c_801])).
% 4.50/1.81  tff(c_22, plain, (![A_13]: (k1_relat_1(k4_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.50/1.81  tff(c_808, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_804, c_22])).
% 4.50/1.81  tff(c_815, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_808])).
% 4.50/1.81  tff(c_727, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_221])).
% 4.50/1.81  tff(c_915, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_727, c_912])).
% 4.50/1.81  tff(c_934, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_815, c_915])).
% 4.50/1.81  tff(c_982, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_979, c_934])).
% 4.50/1.81  tff(c_1370, plain, (![B_185, C_186, A_187]: (k1_xboole_0=B_185 | v1_funct_2(C_186, A_187, B_185) | k1_relset_1(A_187, B_185, C_186)!=A_187 | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_185))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.50/1.81  tff(c_1383, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_727, c_1370])).
% 4.50/1.81  tff(c_1408, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_982, c_1383])).
% 4.50/1.81  tff(c_1410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_726, c_1094, c_1408])).
% 4.50/1.81  tff(c_1411, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_288])).
% 4.50/1.81  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.50/1.81  tff(c_1425, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1411, c_1411, c_24])).
% 4.50/1.81  tff(c_28, plain, (![A_14]: (k2_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.50/1.81  tff(c_287, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_279, c_28])).
% 4.50/1.81  tff(c_728, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_287])).
% 4.50/1.81  tff(c_1413, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1411, c_728])).
% 4.50/1.81  tff(c_1457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1425, c_1413])).
% 4.50/1.81  tff(c_1458, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_287])).
% 4.50/1.81  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.50/1.81  tff(c_1472, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1458, c_26])).
% 4.50/1.81  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.50/1.81  tff(c_1468, plain, (![A_7]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_12])).
% 4.50/1.81  tff(c_1837, plain, (![A_236, B_237, C_238]: (k1_relset_1(A_236, B_237, C_238)=k1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.50/1.81  tff(c_1841, plain, (![A_236, B_237]: (k1_relset_1(A_236, B_237, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1468, c_1837])).
% 4.50/1.81  tff(c_1853, plain, (![A_236, B_237]: (k1_relset_1(A_236, B_237, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1472, c_1841])).
% 4.50/1.81  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.50/1.81  tff(c_54, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.50/1.81  tff(c_76, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_54])).
% 4.50/1.81  tff(c_2347, plain, (![C_303, B_304]: (v1_funct_2(C_303, '#skF_3', B_304) | k1_relset_1('#skF_3', B_304, C_303)!='#skF_3' | ~m1_subset_1(C_303, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1458, c_1458, c_1458, c_76])).
% 4.50/1.81  tff(c_2355, plain, (![B_304]: (v1_funct_2('#skF_3', '#skF_3', B_304) | k1_relset_1('#skF_3', B_304, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_1468, c_2347])).
% 4.50/1.81  tff(c_2364, plain, (![B_304]: (v1_funct_2('#skF_3', '#skF_3', B_304))), inference(demodulation, [status(thm), theory('equality')], [c_1853, c_2355])).
% 4.50/1.81  tff(c_1459, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_287])).
% 4.50/1.81  tff(c_1486, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1459])).
% 4.50/1.81  tff(c_1763, plain, (![A_221, B_222, C_223]: (k2_relset_1(A_221, B_222, C_223)=k2_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.50/1.81  tff(c_1767, plain, (![A_221, B_222]: (k2_relset_1(A_221, B_222, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1468, c_1763])).
% 4.50/1.81  tff(c_1779, plain, (![A_221, B_222]: (k2_relset_1(A_221, B_222, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1767])).
% 4.50/1.81  tff(c_1781, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_64])).
% 4.50/1.81  tff(c_1538, plain, (![A_193]: (k4_relat_1(A_193)=k2_funct_1(A_193) | ~v2_funct_1(A_193) | ~v1_funct_1(A_193) | ~v1_relat_1(A_193))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.50/1.81  tff(c_1541, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1538])).
% 4.50/1.81  tff(c_1544, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_72, c_1541])).
% 4.50/1.81  tff(c_20, plain, (![A_13]: (k2_relat_1(k4_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.50/1.81  tff(c_1551, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1544, c_20])).
% 4.50/1.81  tff(c_1557, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_1472, c_1551])).
% 4.50/1.81  tff(c_38, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.50/1.81  tff(c_1484, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_727, c_38])).
% 4.50/1.81  tff(c_1641, plain, (![A_209]: (k2_relat_1(A_209)!='#skF_3' | A_209='#skF_3' | ~v1_relat_1(A_209))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1458, c_28])).
% 4.50/1.81  tff(c_1644, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1484, c_1641])).
% 4.50/1.81  tff(c_1653, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1644])).
% 4.50/1.81  tff(c_1688, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1653, c_726])).
% 4.50/1.81  tff(c_1789, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_1688])).
% 4.50/1.81  tff(c_2368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2364, c_1789])).
% 4.50/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.81  
% 4.50/1.81  Inference rules
% 4.50/1.81  ----------------------
% 4.50/1.81  #Ref     : 0
% 4.50/1.81  #Sup     : 523
% 4.50/1.81  #Fact    : 0
% 4.50/1.81  #Define  : 0
% 4.50/1.81  #Split   : 9
% 4.50/1.81  #Chain   : 0
% 4.50/1.81  #Close   : 0
% 4.50/1.81  
% 4.50/1.81  Ordering : KBO
% 4.50/1.81  
% 4.50/1.81  Simplification rules
% 4.50/1.81  ----------------------
% 4.50/1.81  #Subsume      : 29
% 4.50/1.81  #Demod        : 346
% 4.50/1.81  #Tautology    : 245
% 4.50/1.81  #SimpNegUnit  : 7
% 4.50/1.81  #BackRed      : 51
% 4.50/1.81  
% 4.50/1.81  #Partial instantiations: 0
% 4.50/1.81  #Strategies tried      : 1
% 4.50/1.81  
% 4.50/1.81  Timing (in seconds)
% 4.50/1.81  ----------------------
% 4.50/1.81  Preprocessing        : 0.34
% 4.50/1.81  Parsing              : 0.18
% 4.50/1.81  CNF conversion       : 0.02
% 4.50/1.81  Main loop            : 0.60
% 4.50/1.81  Inferencing          : 0.21
% 4.50/1.81  Reduction            : 0.19
% 4.50/1.81  Demodulation         : 0.14
% 4.50/1.81  BG Simplification    : 0.03
% 4.50/1.81  Subsumption          : 0.10
% 4.50/1.81  Abstraction          : 0.03
% 4.50/1.81  MUC search           : 0.00
% 4.50/1.81  Cooper               : 0.00
% 4.50/1.81  Total                : 1.03
% 4.50/1.81  Index Insertion      : 0.00
% 4.50/1.82  Index Deletion       : 0.00
% 4.50/1.82  Index Matching       : 0.00
% 4.50/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
