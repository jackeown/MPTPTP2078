%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:29 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  190 (1356 expanded)
%              Number of leaves         :   39 ( 457 expanded)
%              Depth                    :   15
%              Number of atoms          :  337 (3718 expanded)
%              Number of equality atoms :   76 ( 710 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2031,plain,(
    ! [C_209,A_210,B_211] :
      ( v1_xboole_0(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ v1_xboole_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2049,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_2031])).

tff(c_2054,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2049])).

tff(c_166,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_178,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_166])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2137,plain,(
    ! [A_219,B_220,C_221] :
      ( k2_relset_1(A_219,B_220,C_221) = k2_relat_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2146,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2137])).

tff(c_2160,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2146])).

tff(c_30,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_10] :
      ( v1_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_141,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_144,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_147,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_144])).

tff(c_148,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_151,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_148])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_151])).

tff(c_164,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_198,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_263,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_277,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_263])).

tff(c_643,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_655,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_643])).

tff(c_673,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_277,c_655])).

tff(c_677,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_673])).

tff(c_28,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_165,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_239,plain,(
    ! [A_60] :
      ( k2_relat_1(k2_funct_1(A_60)) = k1_relat_1(A_60)
      | ~ v2_funct_1(A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_28] :
      ( v1_funct_2(A_28,k1_relat_1(A_28),k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_913,plain,(
    ! [A_125] :
      ( v1_funct_2(k2_funct_1(A_125),k1_relat_1(k2_funct_1(A_125)),k1_relat_1(A_125))
      | ~ v1_funct_1(k2_funct_1(A_125))
      | ~ v1_relat_1(k2_funct_1(A_125))
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_54])).

tff(c_916,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_913])).

tff(c_927,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_68,c_165,c_916])).

tff(c_930,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_927])).

tff(c_933,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_930])).

tff(c_937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_933])).

tff(c_939,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_927])).

tff(c_280,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_283,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_280])).

tff(c_295,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_283])).

tff(c_349,plain,(
    ! [A_80] :
      ( m1_subset_1(A_80,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_80),k2_relat_1(A_80))))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1010,plain,(
    ! [A_129] :
      ( m1_subset_1(k2_funct_1(A_129),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_129),k2_relat_1(k2_funct_1(A_129)))))
      | ~ v1_funct_1(k2_funct_1(A_129))
      | ~ v1_relat_1(k2_funct_1(A_129))
      | ~ v2_funct_1(A_129)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_349])).

tff(c_1033,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_1010])).

tff(c_1051,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_68,c_939,c_165,c_1033])).

tff(c_1076,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1051])).

tff(c_1089,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_68,c_677,c_1076])).

tff(c_1091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_1089])).

tff(c_1092,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1120,plain,(
    ! [A_2] : r1_tarski('#skF_2',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_6])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_596,plain,(
    ! [B_96,A_97] :
      ( m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_96),A_97)))
      | ~ r1_tarski(k2_relat_1(B_96),A_97)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_628,plain,(
    ! [B_98] :
      ( m1_subset_1(B_98,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_98),k1_xboole_0)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_596])).

tff(c_631,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_628])).

tff(c_639,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_631])).

tff(c_642,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_1095,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_642])).

tff(c_1200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1120,c_1095])).

tff(c_1201,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_203,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_xboole_0(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_213,plain,(
    ! [C_50] :
      ( v1_xboole_0(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_203])).

tff(c_221,plain,(
    ! [C_50] :
      ( v1_xboole_0(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_213])).

tff(c_1228,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1201,c_221])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1240,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1228,c_4])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1266,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_1240,c_20])).

tff(c_366,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_349])).

tff(c_385,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_366])).

tff(c_34,plain,(
    ! [C_18,A_15,B_16] :
      ( v1_xboole_0(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_408,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_385,c_34])).

tff(c_411,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_408])).

tff(c_1346,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_411])).

tff(c_1349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1346])).

tff(c_1350,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_408])).

tff(c_1360,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1350,c_4])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1376,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_14])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1379,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_1360,c_18])).

tff(c_1681,plain,(
    ! [A_165] :
      ( v1_xboole_0(A_165)
      | ~ v1_xboole_0(k1_relat_1(A_165))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_349,c_34])).

tff(c_1947,plain,(
    ! [A_199] :
      ( v1_xboole_0(k2_funct_1(A_199))
      | ~ v1_xboole_0(k2_relat_1(A_199))
      | ~ v1_funct_1(k2_funct_1(A_199))
      | ~ v1_relat_1(k2_funct_1(A_199))
      | ~ v2_funct_1(A_199)
      | ~ v1_funct_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1681])).

tff(c_1950,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_1947])).

tff(c_1955,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_68,c_165,c_1350,c_1950])).

tff(c_1968,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1955])).

tff(c_1971,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1968])).

tff(c_1975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_1971])).

tff(c_1976,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1955])).

tff(c_1375,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_4])).

tff(c_1996,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1976,c_1375])).

tff(c_1377,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_1360,c_12])).

tff(c_1396,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_295])).

tff(c_1415,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_198])).

tff(c_1667,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_1415])).

tff(c_2001,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1996,c_1667])).

tff(c_2007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_2001])).

tff(c_2008,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_2009,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_2163,plain,(
    ! [A_222,B_223,C_224] :
      ( k1_relset_1(A_222,B_223,C_224) = k1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2184,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2009,c_2163])).

tff(c_2652,plain,(
    ! [B_262,C_263,A_264] :
      ( k1_xboole_0 = B_262
      | v1_funct_2(C_263,A_264,B_262)
      | k1_relset_1(A_264,B_262,C_263) != A_264
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_264,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2664,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2009,c_2652])).

tff(c_2682,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2184,c_2664])).

tff(c_2683,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2008,c_2682])).

tff(c_2690,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2683])).

tff(c_2693,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2690])).

tff(c_2696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_74,c_68,c_2160,c_2693])).

tff(c_2697,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2683])).

tff(c_2728,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2697,c_2])).

tff(c_2730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2054,c_2728])).

tff(c_2732,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2049])).

tff(c_2749,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2732,c_4])).

tff(c_2731,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2049])).

tff(c_2741,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2731,c_4])).

tff(c_2772,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2749,c_2741])).

tff(c_179,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_166])).

tff(c_118,plain,(
    ! [A_36] :
      ( v1_funct_1(A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_118])).

tff(c_180,plain,(
    ! [A_48] :
      ( v1_funct_2(A_48,k1_relat_1(A_48),k2_relat_1(A_48))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_186,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_180])).

tff(c_190,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_18,c_186])).

tff(c_2011,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_190])).

tff(c_2751,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2741,c_2741,c_2741,c_2011])).

tff(c_2879,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_2772,c_2772,c_2751])).

tff(c_40,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_25,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_76,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_2755,plain,(
    ! [A_25] :
      ( v1_funct_2('#skF_3',A_25,'#skF_3')
      | A_25 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2741,c_2741,c_2741,c_76])).

tff(c_2942,plain,(
    ! [A_25] :
      ( v1_funct_2('#skF_1',A_25,'#skF_1')
      | A_25 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_2772,c_2772,c_2755])).

tff(c_2760,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2741,c_2741,c_10])).

tff(c_2866,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_2772,c_2760])).

tff(c_2781,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_2009])).

tff(c_2984,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2866,c_2781])).

tff(c_2044,plain,(
    ! [C_209] :
      ( v1_xboole_0(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2031])).

tff(c_2053,plain,(
    ! [C_209] :
      ( v1_xboole_0(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2044])).

tff(c_2931,plain,(
    ! [C_209] :
      ( v1_xboole_0(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2749,c_2053])).

tff(c_2995,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2984,c_2931])).

tff(c_2757,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2741,c_4])).

tff(c_2830,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_2757])).

tff(c_3004,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2995,c_2830])).

tff(c_2782,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_2008])).

tff(c_3009,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3004,c_2782])).

tff(c_3043,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2942,c_3009])).

tff(c_3044,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3043,c_3009])).

tff(c_3050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2879,c_3044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.87  
% 4.89/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.87  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.89/1.87  
% 4.89/1.87  %Foreground sorts:
% 4.89/1.87  
% 4.89/1.87  
% 4.89/1.87  %Background operators:
% 4.89/1.87  
% 4.89/1.87  
% 4.89/1.87  %Foreground operators:
% 4.89/1.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.89/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.89/1.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.89/1.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.89/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.89/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.89/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.89/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.89/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.89/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.89/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.89/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.89/1.87  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.89/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.89/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.89/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.89/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.89/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.89/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.89/1.87  
% 4.89/1.89  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.89/1.89  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.89/1.89  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.89/1.89  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.89/1.89  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.89/1.89  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.89/1.89  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.89/1.89  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.89/1.89  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.89/1.89  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.89/1.89  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.89/1.89  tff(f_130, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.89/1.89  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.89/1.89  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.89/1.89  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.89/1.89  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.89/1.89  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 4.89/1.89  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.89/1.89  tff(c_2031, plain, (![C_209, A_210, B_211]: (v1_xboole_0(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~v1_xboole_0(A_210))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.89/1.89  tff(c_2049, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_2031])).
% 4.89/1.89  tff(c_2054, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2049])).
% 4.89/1.89  tff(c_166, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.89/1.89  tff(c_178, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_166])).
% 4.89/1.89  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.89/1.89  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.89/1.89  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.89/1.89  tff(c_2137, plain, (![A_219, B_220, C_221]: (k2_relset_1(A_219, B_220, C_221)=k2_relat_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.89/1.89  tff(c_2146, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2137])).
% 4.89/1.89  tff(c_2160, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2146])).
% 4.89/1.89  tff(c_30, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.89/1.89  tff(c_24, plain, (![A_10]: (v1_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.89/1.89  tff(c_64, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.89/1.89  tff(c_141, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 4.89/1.89  tff(c_144, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_141])).
% 4.89/1.89  tff(c_147, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_144])).
% 4.89/1.89  tff(c_148, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.89/1.89  tff(c_151, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_148])).
% 4.89/1.89  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_151])).
% 4.89/1.89  tff(c_164, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 4.89/1.89  tff(c_198, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_164])).
% 4.89/1.89  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.89/1.89  tff(c_263, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.89/1.89  tff(c_277, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_263])).
% 4.89/1.89  tff(c_643, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.89/1.89  tff(c_655, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_643])).
% 4.89/1.89  tff(c_673, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_277, c_655])).
% 4.89/1.89  tff(c_677, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_673])).
% 4.89/1.89  tff(c_28, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.89/1.89  tff(c_26, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.89/1.89  tff(c_165, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 4.89/1.89  tff(c_239, plain, (![A_60]: (k2_relat_1(k2_funct_1(A_60))=k1_relat_1(A_60) | ~v2_funct_1(A_60) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.89/1.89  tff(c_54, plain, (![A_28]: (v1_funct_2(A_28, k1_relat_1(A_28), k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.89/1.89  tff(c_913, plain, (![A_125]: (v1_funct_2(k2_funct_1(A_125), k1_relat_1(k2_funct_1(A_125)), k1_relat_1(A_125)) | ~v1_funct_1(k2_funct_1(A_125)) | ~v1_relat_1(k2_funct_1(A_125)) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_239, c_54])).
% 4.89/1.89  tff(c_916, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_677, c_913])).
% 4.89/1.89  tff(c_927, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_68, c_165, c_916])).
% 4.89/1.89  tff(c_930, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_927])).
% 4.89/1.89  tff(c_933, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_930])).
% 4.89/1.89  tff(c_937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_933])).
% 4.89/1.89  tff(c_939, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_927])).
% 4.89/1.89  tff(c_280, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.89/1.89  tff(c_283, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_280])).
% 4.89/1.89  tff(c_295, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_283])).
% 4.89/1.89  tff(c_349, plain, (![A_80]: (m1_subset_1(A_80, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_80), k2_relat_1(A_80)))) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.89/1.89  tff(c_1010, plain, (![A_129]: (m1_subset_1(k2_funct_1(A_129), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_129), k2_relat_1(k2_funct_1(A_129))))) | ~v1_funct_1(k2_funct_1(A_129)) | ~v1_relat_1(k2_funct_1(A_129)) | ~v2_funct_1(A_129) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(superposition, [status(thm), theory('equality')], [c_30, c_349])).
% 4.89/1.89  tff(c_1033, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_295, c_1010])).
% 4.89/1.89  tff(c_1051, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_68, c_939, c_165, c_1033])).
% 4.89/1.89  tff(c_1076, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1051])).
% 4.89/1.89  tff(c_1089, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_68, c_677, c_1076])).
% 4.89/1.89  tff(c_1091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_1089])).
% 4.89/1.89  tff(c_1092, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_673])).
% 4.89/1.89  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.89/1.89  tff(c_1120, plain, (![A_2]: (r1_tarski('#skF_2', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_6])).
% 4.89/1.89  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.89/1.89  tff(c_596, plain, (![B_96, A_97]: (m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_96), A_97))) | ~r1_tarski(k2_relat_1(B_96), A_97) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.89/1.89  tff(c_628, plain, (![B_98]: (m1_subset_1(B_98, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_98), k1_xboole_0) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(superposition, [status(thm), theory('equality')], [c_10, c_596])).
% 4.89/1.89  tff(c_631, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_295, c_628])).
% 4.89/1.89  tff(c_639, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_631])).
% 4.89/1.89  tff(c_642, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_639])).
% 4.89/1.89  tff(c_1095, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_642])).
% 4.89/1.89  tff(c_1200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1120, c_1095])).
% 4.89/1.89  tff(c_1201, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_639])).
% 4.89/1.89  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.89/1.89  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.89/1.89  tff(c_203, plain, (![C_50, A_51, B_52]: (v1_xboole_0(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.89/1.89  tff(c_213, plain, (![C_50]: (v1_xboole_0(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_203])).
% 4.89/1.89  tff(c_221, plain, (![C_50]: (v1_xboole_0(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_213])).
% 4.89/1.89  tff(c_1228, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1201, c_221])).
% 4.89/1.89  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.89/1.89  tff(c_1240, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1228, c_4])).
% 4.89/1.89  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.89/1.89  tff(c_1266, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_1240, c_20])).
% 4.89/1.89  tff(c_366, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_295, c_349])).
% 4.89/1.89  tff(c_385, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_366])).
% 4.89/1.89  tff(c_34, plain, (![C_18, A_15, B_16]: (v1_xboole_0(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.89/1.89  tff(c_408, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_385, c_34])).
% 4.89/1.89  tff(c_411, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_408])).
% 4.89/1.89  tff(c_1346, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_411])).
% 4.89/1.90  tff(c_1349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1228, c_1346])).
% 4.89/1.90  tff(c_1350, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_408])).
% 4.89/1.90  tff(c_1360, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1350, c_4])).
% 4.89/1.90  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.89/1.90  tff(c_1376, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_14])).
% 4.89/1.90  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.89/1.90  tff(c_1379, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_1360, c_18])).
% 4.89/1.90  tff(c_1681, plain, (![A_165]: (v1_xboole_0(A_165) | ~v1_xboole_0(k1_relat_1(A_165)) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(resolution, [status(thm)], [c_349, c_34])).
% 4.89/1.90  tff(c_1947, plain, (![A_199]: (v1_xboole_0(k2_funct_1(A_199)) | ~v1_xboole_0(k2_relat_1(A_199)) | ~v1_funct_1(k2_funct_1(A_199)) | ~v1_relat_1(k2_funct_1(A_199)) | ~v2_funct_1(A_199) | ~v1_funct_1(A_199) | ~v1_relat_1(A_199))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1681])).
% 4.89/1.90  tff(c_1950, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1379, c_1947])).
% 4.89/1.90  tff(c_1955, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_68, c_165, c_1350, c_1950])).
% 4.89/1.90  tff(c_1968, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1955])).
% 4.89/1.90  tff(c_1971, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1968])).
% 4.89/1.90  tff(c_1975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_1971])).
% 4.89/1.90  tff(c_1976, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1955])).
% 4.89/1.90  tff(c_1375, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_4])).
% 4.89/1.90  tff(c_1996, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1976, c_1375])).
% 4.89/1.90  tff(c_1377, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_1360, c_12])).
% 4.89/1.90  tff(c_1396, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_295])).
% 4.89/1.90  tff(c_1415, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_198])).
% 4.89/1.90  tff(c_1667, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_1415])).
% 4.89/1.90  tff(c_2001, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1996, c_1667])).
% 4.89/1.90  tff(c_2007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1376, c_2001])).
% 4.89/1.90  tff(c_2008, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_164])).
% 4.89/1.90  tff(c_2009, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_164])).
% 4.89/1.90  tff(c_2163, plain, (![A_222, B_223, C_224]: (k1_relset_1(A_222, B_223, C_224)=k1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.89/1.90  tff(c_2184, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2009, c_2163])).
% 4.89/1.90  tff(c_2652, plain, (![B_262, C_263, A_264]: (k1_xboole_0=B_262 | v1_funct_2(C_263, A_264, B_262) | k1_relset_1(A_264, B_262, C_263)!=A_264 | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_264, B_262))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.89/1.90  tff(c_2664, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2009, c_2652])).
% 4.89/1.90  tff(c_2682, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2184, c_2664])).
% 4.89/1.90  tff(c_2683, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2008, c_2682])).
% 4.89/1.90  tff(c_2690, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_2683])).
% 4.89/1.90  tff(c_2693, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2690])).
% 4.89/1.90  tff(c_2696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_74, c_68, c_2160, c_2693])).
% 4.89/1.90  tff(c_2697, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2683])).
% 4.89/1.90  tff(c_2728, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2697, c_2])).
% 4.89/1.90  tff(c_2730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2054, c_2728])).
% 4.89/1.90  tff(c_2732, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_2049])).
% 4.89/1.90  tff(c_2749, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2732, c_4])).
% 4.89/1.90  tff(c_2731, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_2049])).
% 4.89/1.90  tff(c_2741, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2731, c_4])).
% 4.89/1.90  tff(c_2772, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2749, c_2741])).
% 4.89/1.90  tff(c_179, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_166])).
% 4.89/1.90  tff(c_118, plain, (![A_36]: (v1_funct_1(A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.89/1.90  tff(c_122, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_118])).
% 4.89/1.90  tff(c_180, plain, (![A_48]: (v1_funct_2(A_48, k1_relat_1(A_48), k2_relat_1(A_48)) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.89/1.90  tff(c_186, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k2_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_180])).
% 4.89/1.90  tff(c_190, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_18, c_186])).
% 4.89/1.90  tff(c_2011, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_190])).
% 4.89/1.90  tff(c_2751, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2741, c_2741, c_2741, c_2011])).
% 4.89/1.90  tff(c_2879, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_2772, c_2772, c_2751])).
% 4.89/1.90  tff(c_40, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_25, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.89/1.90  tff(c_76, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 4.89/1.90  tff(c_2755, plain, (![A_25]: (v1_funct_2('#skF_3', A_25, '#skF_3') | A_25='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2741, c_2741, c_2741, c_76])).
% 4.89/1.90  tff(c_2942, plain, (![A_25]: (v1_funct_2('#skF_1', A_25, '#skF_1') | A_25='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_2772, c_2772, c_2755])).
% 4.89/1.90  tff(c_2760, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2741, c_2741, c_10])).
% 4.89/1.90  tff(c_2866, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_2772, c_2760])).
% 4.89/1.90  tff(c_2781, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_2009])).
% 4.89/1.90  tff(c_2984, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2866, c_2781])).
% 4.89/1.90  tff(c_2044, plain, (![C_209]: (v1_xboole_0(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2031])).
% 4.89/1.90  tff(c_2053, plain, (![C_209]: (v1_xboole_0(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2044])).
% 4.89/1.90  tff(c_2931, plain, (![C_209]: (v1_xboole_0(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2749, c_2053])).
% 4.89/1.90  tff(c_2995, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_2984, c_2931])).
% 4.89/1.90  tff(c_2757, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2741, c_4])).
% 4.89/1.90  tff(c_2830, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_2757])).
% 4.89/1.90  tff(c_3004, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_2995, c_2830])).
% 4.89/1.90  tff(c_2782, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_2008])).
% 4.89/1.90  tff(c_3009, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3004, c_2782])).
% 4.89/1.90  tff(c_3043, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_2942, c_3009])).
% 4.89/1.90  tff(c_3044, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3043, c_3009])).
% 4.89/1.90  tff(c_3050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2879, c_3044])).
% 4.89/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.90  
% 4.89/1.90  Inference rules
% 4.89/1.90  ----------------------
% 4.89/1.90  #Ref     : 0
% 4.89/1.90  #Sup     : 611
% 4.89/1.90  #Fact    : 0
% 4.89/1.90  #Define  : 0
% 4.89/1.90  #Split   : 17
% 4.89/1.90  #Chain   : 0
% 4.89/1.90  #Close   : 0
% 4.89/1.90  
% 4.89/1.90  Ordering : KBO
% 4.89/1.90  
% 4.89/1.90  Simplification rules
% 4.89/1.90  ----------------------
% 4.89/1.90  #Subsume      : 82
% 4.89/1.90  #Demod        : 1053
% 4.89/1.90  #Tautology    : 344
% 4.89/1.90  #SimpNegUnit  : 4
% 4.89/1.90  #BackRed      : 189
% 4.89/1.90  
% 4.89/1.90  #Partial instantiations: 0
% 4.89/1.90  #Strategies tried      : 1
% 4.89/1.90  
% 4.89/1.90  Timing (in seconds)
% 4.89/1.90  ----------------------
% 4.89/1.90  Preprocessing        : 0.35
% 4.89/1.90  Parsing              : 0.19
% 4.89/1.90  CNF conversion       : 0.02
% 4.89/1.90  Main loop            : 0.73
% 4.89/1.90  Inferencing          : 0.27
% 4.89/1.90  Reduction            : 0.25
% 4.89/1.90  Demodulation         : 0.18
% 4.89/1.90  BG Simplification    : 0.03
% 4.89/1.90  Subsumption          : 0.12
% 4.89/1.90  Abstraction          : 0.03
% 4.89/1.90  MUC search           : 0.00
% 4.89/1.90  Cooper               : 0.00
% 4.89/1.90  Total                : 1.14
% 4.89/1.90  Index Insertion      : 0.00
% 4.89/1.90  Index Deletion       : 0.00
% 4.89/1.90  Index Matching       : 0.00
% 4.89/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
