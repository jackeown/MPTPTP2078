%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:25 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  269 (3052 expanded)
%              Number of leaves         :   44 ( 980 expanded)
%              Depth                    :   17
%              Number of atoms          :  471 (7746 expanded)
%              Number of equality atoms :  150 (1595 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_170,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_153,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_152,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_164,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_152])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_183,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_xboole_0(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_197,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_183])).

tff(c_202,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1391,plain,(
    ! [A_161,B_162,C_163] :
      ( k2_relset_1(A_161,B_162,C_163) = k2_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1400,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1391])).

tff(c_1414,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1400])).

tff(c_30,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_210,plain,(
    ! [C_63,B_64,A_65] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(B_64,A_65)))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_224,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_210])).

tff(c_229,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_22,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_166,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_169,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_169])).

tff(c_174,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_295,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_389,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_395,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_389])).

tff(c_408,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_395])).

tff(c_24,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_240,plain,(
    ! [A_73] :
      ( k1_relat_1(k2_funct_1(A_73)) = k2_relat_1(A_73)
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1030,plain,(
    ! [A_149] :
      ( k9_relat_1(k2_funct_1(A_149),k2_relat_1(A_149)) = k2_relat_1(k2_funct_1(A_149))
      | ~ v1_relat_1(k2_funct_1(A_149))
      | ~ v2_funct_1(A_149)
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_16])).

tff(c_1046,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_1030])).

tff(c_1053,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_70,c_1046])).

tff(c_1054,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1053])).

tff(c_1057,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1054])).

tff(c_1061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_1057])).

tff(c_1063,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1053])).

tff(c_175,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_301,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_315,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_301])).

tff(c_835,plain,(
    ! [B_137,A_138,C_139] :
      ( k1_xboole_0 = B_137
      | k1_relset_1(A_138,B_137,C_139) = A_138
      | ~ v1_funct_2(C_139,A_138,B_137)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_844,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_835])).

tff(c_861,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_315,c_844])).

tff(c_865,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_861])).

tff(c_18,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_422,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_18])).

tff(c_432,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_422])).

tff(c_871,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_432])).

tff(c_1062,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1053])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(k2_funct_1(B_13),A_12) = k10_relat_1(B_13,A_12)
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1067,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_26])).

tff(c_1074,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_70,c_871,c_1067])).

tff(c_60,plain,(
    ! [A_42] :
      ( m1_subset_1(A_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_42),k2_relat_1(A_42))))
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1119,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_60])).

tff(c_1145,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_175,c_1119])).

tff(c_1241,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1145])).

tff(c_1260,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_70,c_408,c_1241])).

tff(c_1262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_1260])).

tff(c_1263,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_861])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1296,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_2])).

tff(c_1298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_1296])).

tff(c_1299,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_1300,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_1326,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relset_1(A_155,B_156,C_157) = k1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1343,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1300,c_1326])).

tff(c_2041,plain,(
    ! [B_223,C_224,A_225] :
      ( k1_xboole_0 = B_223
      | v1_funct_2(C_224,A_225,B_223)
      | k1_relset_1(A_225,B_223,C_224) != A_225
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2047,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1300,c_2041])).

tff(c_2063,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_2047])).

tff(c_2064,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1299,c_2063])).

tff(c_2073,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2064])).

tff(c_2076,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2073])).

tff(c_2079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_70,c_1414,c_2076])).

tff(c_2080,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2064])).

tff(c_2113,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2])).

tff(c_2115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_2113])).

tff(c_2116,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2126,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2116,c_4])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2142,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_2126,c_10])).

tff(c_2117,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_2134,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2117,c_4])).

tff(c_2157,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_2134])).

tff(c_2303,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2142,c_2157,c_2157,c_174])).

tff(c_2304,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2303])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2141,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_12])).

tff(c_2366,plain,(
    ! [A_254,B_255,C_256] :
      ( k1_relset_1(A_254,B_255,C_256) = k1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2381,plain,(
    ! [A_254,B_255] : k1_relset_1(A_254,B_255,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2141,c_2366])).

tff(c_52,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_80,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_2535,plain,(
    ! [C_278,B_279] :
      ( v1_funct_2(C_278,'#skF_3',B_279)
      | k1_relset_1('#skF_3',B_279,C_278) != '#skF_3'
      | ~ m1_subset_1(C_278,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_2126,c_2126,c_2126,c_80])).

tff(c_2538,plain,(
    ! [B_279] :
      ( v1_funct_2('#skF_3','#skF_3',B_279)
      | k1_relset_1('#skF_3',B_279,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_2141,c_2535])).

tff(c_2540,plain,(
    ! [B_279] :
      ( v1_funct_2('#skF_3','#skF_3',B_279)
      | k1_relat_1('#skF_3') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2381,c_2538])).

tff(c_2541,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2540])).

tff(c_2289,plain,(
    ! [C_243,A_244,B_245] :
      ( v1_partfun1(C_243,A_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_xboole_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2296,plain,(
    ! [C_243] :
      ( v1_partfun1(C_243,'#skF_3')
      | ~ m1_subset_1(C_243,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2142,c_2289])).

tff(c_2306,plain,(
    ! [C_247] :
      ( v1_partfun1(C_247,'#skF_3')
      | ~ m1_subset_1(C_247,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2296])).

tff(c_2311,plain,(
    v1_partfun1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2141,c_2306])).

tff(c_2615,plain,(
    ! [C_287,A_288,B_289] :
      ( v1_funct_2(C_287,A_288,B_289)
      | ~ v1_partfun1(C_287,A_288)
      | ~ v1_funct_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2622,plain,(
    ! [A_288,B_289] :
      ( v1_funct_2('#skF_3',A_288,B_289)
      | ~ v1_partfun1('#skF_3',A_288)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2141,c_2615])).

tff(c_2633,plain,(
    ! [A_290,B_291] :
      ( v1_funct_2('#skF_3',A_290,B_291)
      | ~ v1_partfun1('#skF_3',A_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2622])).

tff(c_56,plain,(
    ! [B_40,C_41] :
      ( k1_relset_1(k1_xboole_0,B_40,C_41) = k1_xboole_0
      | ~ v1_funct_2(C_41,k1_xboole_0,B_40)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_79,plain,(
    ! [B_40,C_41] :
      ( k1_relset_1(k1_xboole_0,B_40,C_41) = k1_xboole_0
      | ~ v1_funct_2(C_41,k1_xboole_0,B_40)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_2593,plain,(
    ! [B_40,C_41] :
      ( k1_relset_1('#skF_3',B_40,C_41) = '#skF_3'
      | ~ v1_funct_2(C_41,'#skF_3',B_40)
      | ~ m1_subset_1(C_41,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_2126,c_2126,c_2126,c_79])).

tff(c_2636,plain,(
    ! [B_291] :
      ( k1_relset_1('#skF_3',B_291,'#skF_3') = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
      | ~ v1_partfun1('#skF_3','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2633,c_2593])).

tff(c_2642,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_2141,c_2381,c_2636])).

tff(c_2644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2541,c_2642])).

tff(c_2646,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2540])).

tff(c_2274,plain,(
    ! [A_242] :
      ( k2_relat_1(k2_funct_1(A_242)) = k1_relat_1(A_242)
      | ~ v2_funct_1(A_242)
      | ~ v1_funct_1(A_242)
      | ~ v1_relat_1(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2942,plain,(
    ! [A_322] :
      ( k10_relat_1(k2_funct_1(A_322),k1_relat_1(A_322)) = k1_relat_1(k2_funct_1(A_322))
      | ~ v1_relat_1(k2_funct_1(A_322))
      | ~ v2_funct_1(A_322)
      | ~ v1_funct_1(A_322)
      | ~ v1_relat_1(A_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2274,c_18])).

tff(c_2951,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2646,c_2942])).

tff(c_2958,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_70,c_2951])).

tff(c_2959,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2958])).

tff(c_2962,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2959])).

tff(c_2966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_2962])).

tff(c_2968,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2958])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2144,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_2126,c_8])).

tff(c_2405,plain,(
    ! [A_264,B_265,C_266] :
      ( k2_relset_1(A_264,B_265,C_266) = k2_relat_1(C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2435,plain,(
    ! [A_269,B_270] : k2_relset_1(A_269,B_270,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2141,c_2405])).

tff(c_2161,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2157,c_2157,c_68])).

tff(c_2439,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2435,c_2161])).

tff(c_2459,plain,
    ( k10_relat_1('#skF_3','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2439,c_18])).

tff(c_2469,plain,(
    k10_relat_1('#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_2459])).

tff(c_2647,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2646,c_2469])).

tff(c_2317,plain,(
    ! [A_250] :
      ( k1_relat_1(k2_funct_1(A_250)) = k2_relat_1(A_250)
      | ~ v2_funct_1(A_250)
      | ~ v1_funct_1(A_250)
      | ~ v1_relat_1(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2969,plain,(
    ! [A_323] :
      ( k9_relat_1(k2_funct_1(A_323),k2_relat_1(A_323)) = k2_relat_1(k2_funct_1(A_323))
      | ~ v1_relat_1(k2_funct_1(A_323))
      | ~ v2_funct_1(A_323)
      | ~ v1_funct_1(A_323)
      | ~ v1_relat_1(A_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2317,c_16])).

tff(c_2985,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2439,c_2969])).

tff(c_2992,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_70,c_2968,c_2985])).

tff(c_3000,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2992,c_26])).

tff(c_3007,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_70,c_2647,c_3000])).

tff(c_3030,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3007,c_60])).

tff(c_3056,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_175,c_2144,c_3030])).

tff(c_3058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2304,c_3056])).

tff(c_3060,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2303])).

tff(c_193,plain,(
    ! [C_59] :
      ( v1_xboole_0(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_183])).

tff(c_201,plain,(
    ! [C_59] :
      ( v1_xboole_0(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_193])).

tff(c_2135,plain,(
    ! [C_59] :
      ( v1_xboole_0(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_201])).

tff(c_3070,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3060,c_2135])).

tff(c_2143,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_4])).

tff(c_3093,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3070,c_2143])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3111,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3093,c_28])).

tff(c_3123,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_76,c_70,c_3111])).

tff(c_3149,plain,(
    ! [A_326,B_327,C_328] :
      ( k2_relset_1(A_326,B_327,C_328) = k2_relat_1(C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3153,plain,(
    ! [A_326,B_327] : k2_relset_1(A_326,B_327,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2141,c_3149])).

tff(c_3162,plain,(
    ! [A_329,B_330] : k2_relset_1(A_329,B_330,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3123,c_3153])).

tff(c_3166,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_2161])).

tff(c_3297,plain,(
    ! [A_339,B_340,C_341] :
      ( k1_relset_1(A_339,B_340,C_341) = k1_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3304,plain,(
    ! [A_339,B_340] : k1_relset_1(A_339,B_340,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2141,c_3297])).

tff(c_3313,plain,(
    ! [A_339,B_340] : k1_relset_1(A_339,B_340,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3166,c_3304])).

tff(c_3426,plain,(
    ! [C_358,B_359] :
      ( v1_funct_2(C_358,'#skF_3',B_359)
      | k1_relset_1('#skF_3',B_359,C_358) != '#skF_3'
      | ~ m1_subset_1(C_358,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2126,c_2126,c_2126,c_2126,c_80])).

tff(c_3429,plain,(
    ! [B_359] :
      ( v1_funct_2('#skF_3','#skF_3',B_359)
      | k1_relset_1('#skF_3',B_359,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_2141,c_3426])).

tff(c_3432,plain,(
    ! [B_359] : v1_funct_2('#skF_3','#skF_3',B_359) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3313,c_3429])).

tff(c_3059,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2303])).

tff(c_3099,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3093,c_3059])).

tff(c_3436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3432,c_3099])).

tff(c_3438,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_3455,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3438,c_4])).

tff(c_3437,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_3447,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3437,c_4])).

tff(c_4304,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3455,c_3447])).

tff(c_48,plain,(
    ! [A_39] :
      ( v1_funct_2(k1_xboole_0,A_39,k1_xboole_0)
      | k1_xboole_0 = A_39
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_39,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_78,plain,(
    ! [A_39] :
      ( v1_funct_2(k1_xboole_0,A_39,k1_xboole_0)
      | k1_xboole_0 = A_39 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_4290,plain,(
    ! [A_39] :
      ( v1_funct_2('#skF_3',A_39,'#skF_3')
      | A_39 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3447,c_3447,c_3447,c_78])).

tff(c_4430,plain,(
    ! [A_453] :
      ( v1_funct_2('#skF_1',A_453,'#skF_1')
      | A_453 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_4304,c_4304,c_4290])).

tff(c_4295,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3447,c_3447,c_8])).

tff(c_4346,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_4304,c_4295])).

tff(c_3474,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3455,c_3447])).

tff(c_3465,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3447,c_3447,c_8])).

tff(c_3494,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_3474,c_3465])).

tff(c_3456,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_3493,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_3456])).

tff(c_3495,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3494,c_3493])).

tff(c_3481,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_164])).

tff(c_20,plain,(
    ! [A_10] :
      ( v1_funct_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3454,plain,(
    v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3438,c_20])).

tff(c_3485,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_70])).

tff(c_3462,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3447,c_12])).

tff(c_3538,plain,(
    ! [A_4] : m1_subset_1('#skF_1',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_3462])).

tff(c_3690,plain,(
    ! [A_394,B_395,C_396] :
      ( k2_relset_1(A_394,B_395,C_396) = k2_relat_1(C_396)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3702,plain,(
    ! [A_397,B_398] : k2_relset_1(A_397,B_398,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3538,c_3690])).

tff(c_3483,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_68])).

tff(c_3706,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3702,c_3483])).

tff(c_3635,plain,(
    ! [A_385] :
      ( k1_relat_1(k2_funct_1(A_385)) = k2_relat_1(A_385)
      | ~ v2_funct_1(A_385)
      | ~ v1_funct_1(A_385)
      | ~ v1_relat_1(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4189,plain,(
    ! [A_447] :
      ( k9_relat_1(k2_funct_1(A_447),k2_relat_1(A_447)) = k2_relat_1(k2_funct_1(A_447))
      | ~ v1_relat_1(k2_funct_1(A_447))
      | ~ v2_funct_1(A_447)
      | ~ v1_funct_1(A_447)
      | ~ v1_relat_1(A_447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3635,c_16])).

tff(c_4205,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3706,c_4189])).

tff(c_4212,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3481,c_3454,c_3485,c_4205])).

tff(c_4213,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4212])).

tff(c_4216,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_4213])).

tff(c_4220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3481,c_3454,c_4216])).

tff(c_4222,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4212])).

tff(c_3480,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_175])).

tff(c_3665,plain,(
    ! [A_387,B_388,C_389] :
      ( k1_relset_1(A_387,B_388,C_389) = k1_relat_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3676,plain,(
    ! [A_387,B_388] : k1_relset_1(A_387,B_388,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3538,c_3665])).

tff(c_3484,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_74])).

tff(c_3858,plain,(
    ! [B_414,C_415] :
      ( k1_relset_1('#skF_1',B_414,C_415) = '#skF_1'
      | ~ v1_funct_2(C_415,'#skF_1',B_414)
      | ~ m1_subset_1(C_415,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3455,c_3455,c_3455,c_3455,c_79])).

tff(c_3863,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3484,c_3858])).

tff(c_3870,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3538,c_3676,c_3863])).

tff(c_3720,plain,
    ( k10_relat_1('#skF_1','#skF_2') = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3706,c_18])).

tff(c_3726,plain,(
    k10_relat_1('#skF_1','#skF_2') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3481,c_3720])).

tff(c_3871,plain,(
    k10_relat_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3870,c_3726])).

tff(c_4221,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4212])).

tff(c_4226,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k10_relat_1('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4221,c_26])).

tff(c_4233,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3481,c_3454,c_3485,c_3871,c_4226])).

tff(c_4256,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4233,c_60])).

tff(c_4282,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4222,c_3480,c_3494,c_4256])).

tff(c_4284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3495,c_4282])).

tff(c_4286,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_4367,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4346,c_4304,c_4286])).

tff(c_4388,plain,(
    ! [C_452] :
      ( v1_xboole_0(C_452)
      | ~ m1_subset_1(C_452,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3455,c_201])).

tff(c_4398,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4367,c_4388])).

tff(c_4294,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3447,c_4])).

tff(c_4324,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_4294])).

tff(c_4405,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4398,c_4324])).

tff(c_4285,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_4309,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_4285])).

tff(c_4409,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4405,c_4309])).

tff(c_4434,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4430,c_4409])).

tff(c_4450,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4434,c_4409])).

tff(c_4315,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_74])).

tff(c_4452,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4434,c_4315])).

tff(c_4462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4450,c_4452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.19  
% 5.75/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.20  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.75/2.20  
% 5.75/2.20  %Foreground sorts:
% 5.75/2.20  
% 5.75/2.20  
% 5.75/2.20  %Background operators:
% 5.75/2.20  
% 5.75/2.20  
% 5.75/2.20  %Foreground operators:
% 5.75/2.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.75/2.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.20  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.75/2.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.75/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.75/2.20  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.75/2.20  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.20  tff('#skF_1', type, '#skF_1': $i).
% 5.75/2.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.75/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.75/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.20  
% 5.75/2.24  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.75/2.24  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.75/2.24  tff(f_93, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 5.75/2.24  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.75/2.24  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.75/2.24  tff(f_100, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.75/2.24  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.75/2.24  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.75/2.24  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.75/2.24  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.75/2.24  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 5.75/2.24  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 5.75/2.24  tff(f_153, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.75/2.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.75/2.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.75/2.24  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.75/2.24  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.75/2.24  tff(f_125, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 5.75/2.24  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 5.75/2.24  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 5.75/2.24  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.75/2.24  tff(c_152, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.75/2.24  tff(c_164, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_152])).
% 5.75/2.24  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.75/2.24  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.75/2.24  tff(c_183, plain, (![C_59, A_60, B_61]: (v1_xboole_0(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.75/2.24  tff(c_197, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_183])).
% 5.75/2.24  tff(c_202, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_197])).
% 5.75/2.24  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.75/2.24  tff(c_1391, plain, (![A_161, B_162, C_163]: (k2_relset_1(A_161, B_162, C_163)=k2_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.24  tff(c_1400, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1391])).
% 5.75/2.24  tff(c_1414, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1400])).
% 5.75/2.24  tff(c_30, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.24  tff(c_210, plain, (![C_63, B_64, A_65]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(B_64, A_65))) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.75/2.24  tff(c_224, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_210])).
% 5.75/2.24  tff(c_229, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_224])).
% 5.75/2.24  tff(c_22, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.75/2.24  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.75/2.24  tff(c_166, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 5.75/2.24  tff(c_169, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_166])).
% 5.75/2.24  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_169])).
% 5.75/2.24  tff(c_174, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_66])).
% 5.75/2.24  tff(c_295, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_174])).
% 5.75/2.24  tff(c_389, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.24  tff(c_395, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_389])).
% 5.75/2.24  tff(c_408, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_395])).
% 5.75/2.24  tff(c_24, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.75/2.24  tff(c_240, plain, (![A_73]: (k1_relat_1(k2_funct_1(A_73))=k2_relat_1(A_73) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.24  tff(c_16, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.24  tff(c_1030, plain, (![A_149]: (k9_relat_1(k2_funct_1(A_149), k2_relat_1(A_149))=k2_relat_1(k2_funct_1(A_149)) | ~v1_relat_1(k2_funct_1(A_149)) | ~v2_funct_1(A_149) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_240, c_16])).
% 5.75/2.24  tff(c_1046, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_408, c_1030])).
% 5.75/2.24  tff(c_1053, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_70, c_1046])).
% 5.75/2.24  tff(c_1054, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1053])).
% 5.75/2.24  tff(c_1057, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1054])).
% 5.75/2.24  tff(c_1061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_1057])).
% 5.75/2.24  tff(c_1063, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1053])).
% 5.75/2.24  tff(c_175, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 5.75/2.24  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.75/2.24  tff(c_301, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.75/2.24  tff(c_315, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_301])).
% 5.75/2.24  tff(c_835, plain, (![B_137, A_138, C_139]: (k1_xboole_0=B_137 | k1_relset_1(A_138, B_137, C_139)=A_138 | ~v1_funct_2(C_139, A_138, B_137) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.75/2.24  tff(c_844, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_835])).
% 5.75/2.24  tff(c_861, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_315, c_844])).
% 5.75/2.24  tff(c_865, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_861])).
% 5.75/2.24  tff(c_18, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.75/2.24  tff(c_422, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_408, c_18])).
% 5.75/2.24  tff(c_432, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_422])).
% 5.75/2.24  tff(c_871, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_865, c_432])).
% 5.75/2.24  tff(c_1062, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1053])).
% 5.75/2.24  tff(c_26, plain, (![B_13, A_12]: (k9_relat_1(k2_funct_1(B_13), A_12)=k10_relat_1(B_13, A_12) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.75/2.24  tff(c_1067, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1062, c_26])).
% 5.75/2.24  tff(c_1074, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_70, c_871, c_1067])).
% 5.75/2.24  tff(c_60, plain, (![A_42]: (m1_subset_1(A_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_42), k2_relat_1(A_42)))) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.75/2.24  tff(c_1119, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1074, c_60])).
% 5.75/2.24  tff(c_1145, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_175, c_1119])).
% 5.75/2.24  tff(c_1241, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1145])).
% 5.75/2.24  tff(c_1260, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_70, c_408, c_1241])).
% 5.75/2.24  tff(c_1262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_1260])).
% 5.75/2.24  tff(c_1263, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_861])).
% 5.75/2.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.75/2.24  tff(c_1296, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_2])).
% 5.75/2.24  tff(c_1298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_1296])).
% 5.75/2.24  tff(c_1299, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_174])).
% 5.75/2.24  tff(c_1300, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_174])).
% 5.75/2.24  tff(c_1326, plain, (![A_155, B_156, C_157]: (k1_relset_1(A_155, B_156, C_157)=k1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.75/2.24  tff(c_1343, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1300, c_1326])).
% 5.75/2.24  tff(c_2041, plain, (![B_223, C_224, A_225]: (k1_xboole_0=B_223 | v1_funct_2(C_224, A_225, B_223) | k1_relset_1(A_225, B_223, C_224)!=A_225 | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.75/2.24  tff(c_2047, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1300, c_2041])).
% 5.75/2.24  tff(c_2063, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1343, c_2047])).
% 5.75/2.24  tff(c_2064, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1299, c_2063])).
% 5.75/2.24  tff(c_2073, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_2064])).
% 5.75/2.24  tff(c_2076, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2073])).
% 5.75/2.24  tff(c_2079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_70, c_1414, c_2076])).
% 5.75/2.24  tff(c_2080, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2064])).
% 5.75/2.24  tff(c_2113, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2])).
% 5.75/2.24  tff(c_2115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_2113])).
% 5.75/2.24  tff(c_2116, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_224])).
% 5.75/2.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.75/2.24  tff(c_2126, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2116, c_4])).
% 5.75/2.24  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.75/2.24  tff(c_2142, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_2126, c_10])).
% 5.75/2.24  tff(c_2117, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_224])).
% 5.75/2.24  tff(c_2134, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2117, c_4])).
% 5.75/2.24  tff(c_2157, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_2134])).
% 5.75/2.24  tff(c_2303, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2142, c_2157, c_2157, c_174])).
% 5.75/2.24  tff(c_2304, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2303])).
% 5.75/2.24  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.24  tff(c_2141, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_12])).
% 5.75/2.24  tff(c_2366, plain, (![A_254, B_255, C_256]: (k1_relset_1(A_254, B_255, C_256)=k1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.75/2.24  tff(c_2381, plain, (![A_254, B_255]: (k1_relset_1(A_254, B_255, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2141, c_2366])).
% 5.75/2.24  tff(c_52, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.75/2.24  tff(c_80, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 5.75/2.24  tff(c_2535, plain, (![C_278, B_279]: (v1_funct_2(C_278, '#skF_3', B_279) | k1_relset_1('#skF_3', B_279, C_278)!='#skF_3' | ~m1_subset_1(C_278, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_2126, c_2126, c_2126, c_80])).
% 5.75/2.24  tff(c_2538, plain, (![B_279]: (v1_funct_2('#skF_3', '#skF_3', B_279) | k1_relset_1('#skF_3', B_279, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_2141, c_2535])).
% 5.75/2.24  tff(c_2540, plain, (![B_279]: (v1_funct_2('#skF_3', '#skF_3', B_279) | k1_relat_1('#skF_3')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2381, c_2538])).
% 5.75/2.24  tff(c_2541, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_2540])).
% 5.75/2.24  tff(c_2289, plain, (![C_243, A_244, B_245]: (v1_partfun1(C_243, A_244) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_xboole_0(A_244))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.75/2.24  tff(c_2296, plain, (![C_243]: (v1_partfun1(C_243, '#skF_3') | ~m1_subset_1(C_243, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2142, c_2289])).
% 5.75/2.24  tff(c_2306, plain, (![C_247]: (v1_partfun1(C_247, '#skF_3') | ~m1_subset_1(C_247, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2296])).
% 5.75/2.24  tff(c_2311, plain, (v1_partfun1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2141, c_2306])).
% 5.75/2.24  tff(c_2615, plain, (![C_287, A_288, B_289]: (v1_funct_2(C_287, A_288, B_289) | ~v1_partfun1(C_287, A_288) | ~v1_funct_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.75/2.24  tff(c_2622, plain, (![A_288, B_289]: (v1_funct_2('#skF_3', A_288, B_289) | ~v1_partfun1('#skF_3', A_288) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2141, c_2615])).
% 5.75/2.24  tff(c_2633, plain, (![A_290, B_291]: (v1_funct_2('#skF_3', A_290, B_291) | ~v1_partfun1('#skF_3', A_290))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2622])).
% 5.75/2.24  tff(c_56, plain, (![B_40, C_41]: (k1_relset_1(k1_xboole_0, B_40, C_41)=k1_xboole_0 | ~v1_funct_2(C_41, k1_xboole_0, B_40) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.75/2.24  tff(c_79, plain, (![B_40, C_41]: (k1_relset_1(k1_xboole_0, B_40, C_41)=k1_xboole_0 | ~v1_funct_2(C_41, k1_xboole_0, B_40) | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 5.75/2.24  tff(c_2593, plain, (![B_40, C_41]: (k1_relset_1('#skF_3', B_40, C_41)='#skF_3' | ~v1_funct_2(C_41, '#skF_3', B_40) | ~m1_subset_1(C_41, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_2126, c_2126, c_2126, c_79])).
% 5.75/2.24  tff(c_2636, plain, (![B_291]: (k1_relset_1('#skF_3', B_291, '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v1_partfun1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_2633, c_2593])).
% 5.75/2.24  tff(c_2642, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_2141, c_2381, c_2636])).
% 5.75/2.24  tff(c_2644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2541, c_2642])).
% 5.75/2.24  tff(c_2646, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2540])).
% 5.75/2.24  tff(c_2274, plain, (![A_242]: (k2_relat_1(k2_funct_1(A_242))=k1_relat_1(A_242) | ~v2_funct_1(A_242) | ~v1_funct_1(A_242) | ~v1_relat_1(A_242))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.24  tff(c_2942, plain, (![A_322]: (k10_relat_1(k2_funct_1(A_322), k1_relat_1(A_322))=k1_relat_1(k2_funct_1(A_322)) | ~v1_relat_1(k2_funct_1(A_322)) | ~v2_funct_1(A_322) | ~v1_funct_1(A_322) | ~v1_relat_1(A_322))), inference(superposition, [status(thm), theory('equality')], [c_2274, c_18])).
% 5.75/2.24  tff(c_2951, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2646, c_2942])).
% 5.75/2.24  tff(c_2958, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_70, c_2951])).
% 5.75/2.24  tff(c_2959, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2958])).
% 5.75/2.24  tff(c_2962, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2959])).
% 5.75/2.24  tff(c_2966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_2962])).
% 5.75/2.24  tff(c_2968, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2958])).
% 5.75/2.24  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.75/2.24  tff(c_2144, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_2126, c_8])).
% 5.75/2.24  tff(c_2405, plain, (![A_264, B_265, C_266]: (k2_relset_1(A_264, B_265, C_266)=k2_relat_1(C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.24  tff(c_2435, plain, (![A_269, B_270]: (k2_relset_1(A_269, B_270, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2141, c_2405])).
% 5.75/2.24  tff(c_2161, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2157, c_2157, c_68])).
% 5.75/2.24  tff(c_2439, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2435, c_2161])).
% 5.75/2.24  tff(c_2459, plain, (k10_relat_1('#skF_3', '#skF_3')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2439, c_18])).
% 5.75/2.24  tff(c_2469, plain, (k10_relat_1('#skF_3', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_2459])).
% 5.75/2.24  tff(c_2647, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2646, c_2469])).
% 5.75/2.24  tff(c_2317, plain, (![A_250]: (k1_relat_1(k2_funct_1(A_250))=k2_relat_1(A_250) | ~v2_funct_1(A_250) | ~v1_funct_1(A_250) | ~v1_relat_1(A_250))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.24  tff(c_2969, plain, (![A_323]: (k9_relat_1(k2_funct_1(A_323), k2_relat_1(A_323))=k2_relat_1(k2_funct_1(A_323)) | ~v1_relat_1(k2_funct_1(A_323)) | ~v2_funct_1(A_323) | ~v1_funct_1(A_323) | ~v1_relat_1(A_323))), inference(superposition, [status(thm), theory('equality')], [c_2317, c_16])).
% 5.75/2.24  tff(c_2985, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2439, c_2969])).
% 5.75/2.24  tff(c_2992, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_70, c_2968, c_2985])).
% 5.75/2.24  tff(c_3000, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2992, c_26])).
% 5.75/2.24  tff(c_3007, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_70, c_2647, c_3000])).
% 5.75/2.24  tff(c_3030, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3007, c_60])).
% 5.75/2.24  tff(c_3056, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_175, c_2144, c_3030])).
% 5.75/2.24  tff(c_3058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2304, c_3056])).
% 5.75/2.24  tff(c_3060, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2303])).
% 5.75/2.24  tff(c_193, plain, (![C_59]: (v1_xboole_0(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_183])).
% 5.75/2.24  tff(c_201, plain, (![C_59]: (v1_xboole_0(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_193])).
% 5.75/2.24  tff(c_2135, plain, (![C_59]: (v1_xboole_0(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_201])).
% 5.75/2.24  tff(c_3070, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3060, c_2135])).
% 5.75/2.24  tff(c_2143, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_4])).
% 5.75/2.24  tff(c_3093, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_3070, c_2143])).
% 5.75/2.24  tff(c_28, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.24  tff(c_3111, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3093, c_28])).
% 5.75/2.24  tff(c_3123, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_76, c_70, c_3111])).
% 5.75/2.24  tff(c_3149, plain, (![A_326, B_327, C_328]: (k2_relset_1(A_326, B_327, C_328)=k2_relat_1(C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.24  tff(c_3153, plain, (![A_326, B_327]: (k2_relset_1(A_326, B_327, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2141, c_3149])).
% 5.75/2.24  tff(c_3162, plain, (![A_329, B_330]: (k2_relset_1(A_329, B_330, '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3123, c_3153])).
% 5.75/2.24  tff(c_3166, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3162, c_2161])).
% 5.75/2.24  tff(c_3297, plain, (![A_339, B_340, C_341]: (k1_relset_1(A_339, B_340, C_341)=k1_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.75/2.24  tff(c_3304, plain, (![A_339, B_340]: (k1_relset_1(A_339, B_340, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2141, c_3297])).
% 5.75/2.24  tff(c_3313, plain, (![A_339, B_340]: (k1_relset_1(A_339, B_340, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3166, c_3304])).
% 5.75/2.24  tff(c_3426, plain, (![C_358, B_359]: (v1_funct_2(C_358, '#skF_3', B_359) | k1_relset_1('#skF_3', B_359, C_358)!='#skF_3' | ~m1_subset_1(C_358, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2126, c_2126, c_2126, c_2126, c_80])).
% 5.75/2.24  tff(c_3429, plain, (![B_359]: (v1_funct_2('#skF_3', '#skF_3', B_359) | k1_relset_1('#skF_3', B_359, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_2141, c_3426])).
% 5.75/2.24  tff(c_3432, plain, (![B_359]: (v1_funct_2('#skF_3', '#skF_3', B_359))), inference(demodulation, [status(thm), theory('equality')], [c_3313, c_3429])).
% 5.75/2.24  tff(c_3059, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_2303])).
% 5.75/2.24  tff(c_3099, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3093, c_3059])).
% 5.75/2.24  tff(c_3436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3432, c_3099])).
% 5.75/2.24  tff(c_3438, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_197])).
% 5.75/2.24  tff(c_3455, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3438, c_4])).
% 5.75/2.24  tff(c_3437, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_197])).
% 5.75/2.24  tff(c_3447, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3437, c_4])).
% 5.75/2.24  tff(c_4304, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3455, c_3447])).
% 5.75/2.24  tff(c_48, plain, (![A_39]: (v1_funct_2(k1_xboole_0, A_39, k1_xboole_0) | k1_xboole_0=A_39 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_39, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.75/2.24  tff(c_78, plain, (![A_39]: (v1_funct_2(k1_xboole_0, A_39, k1_xboole_0) | k1_xboole_0=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 5.75/2.24  tff(c_4290, plain, (![A_39]: (v1_funct_2('#skF_3', A_39, '#skF_3') | A_39='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3447, c_3447, c_3447, c_78])).
% 5.75/2.24  tff(c_4430, plain, (![A_453]: (v1_funct_2('#skF_1', A_453, '#skF_1') | A_453='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_4304, c_4304, c_4290])).
% 5.75/2.24  tff(c_4295, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3447, c_3447, c_8])).
% 5.75/2.24  tff(c_4346, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_4304, c_4295])).
% 5.75/2.24  tff(c_3474, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3455, c_3447])).
% 5.75/2.24  tff(c_3465, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3447, c_3447, c_8])).
% 5.75/2.24  tff(c_3494, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_3474, c_3465])).
% 5.75/2.24  tff(c_3456, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_174])).
% 5.75/2.24  tff(c_3493, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_3456])).
% 5.75/2.24  tff(c_3495, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3494, c_3493])).
% 5.75/2.24  tff(c_3481, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_164])).
% 5.75/2.24  tff(c_20, plain, (![A_10]: (v1_funct_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.75/2.24  tff(c_3454, plain, (v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_3438, c_20])).
% 5.75/2.24  tff(c_3485, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_70])).
% 5.75/2.24  tff(c_3462, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_3447, c_12])).
% 5.75/2.24  tff(c_3538, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_3462])).
% 5.75/2.24  tff(c_3690, plain, (![A_394, B_395, C_396]: (k2_relset_1(A_394, B_395, C_396)=k2_relat_1(C_396) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.75/2.24  tff(c_3702, plain, (![A_397, B_398]: (k2_relset_1(A_397, B_398, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_3538, c_3690])).
% 5.75/2.24  tff(c_3483, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_68])).
% 5.75/2.24  tff(c_3706, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3702, c_3483])).
% 5.75/2.24  tff(c_3635, plain, (![A_385]: (k1_relat_1(k2_funct_1(A_385))=k2_relat_1(A_385) | ~v2_funct_1(A_385) | ~v1_funct_1(A_385) | ~v1_relat_1(A_385))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.75/2.24  tff(c_4189, plain, (![A_447]: (k9_relat_1(k2_funct_1(A_447), k2_relat_1(A_447))=k2_relat_1(k2_funct_1(A_447)) | ~v1_relat_1(k2_funct_1(A_447)) | ~v2_funct_1(A_447) | ~v1_funct_1(A_447) | ~v1_relat_1(A_447))), inference(superposition, [status(thm), theory('equality')], [c_3635, c_16])).
% 5.75/2.24  tff(c_4205, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3706, c_4189])).
% 5.75/2.24  tff(c_4212, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3481, c_3454, c_3485, c_4205])).
% 5.75/2.24  tff(c_4213, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4212])).
% 5.75/2.24  tff(c_4216, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_4213])).
% 5.75/2.24  tff(c_4220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3481, c_3454, c_4216])).
% 5.75/2.24  tff(c_4222, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4212])).
% 5.75/2.24  tff(c_3480, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_175])).
% 5.75/2.24  tff(c_3665, plain, (![A_387, B_388, C_389]: (k1_relset_1(A_387, B_388, C_389)=k1_relat_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.75/2.24  tff(c_3676, plain, (![A_387, B_388]: (k1_relset_1(A_387, B_388, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_3538, c_3665])).
% 5.75/2.24  tff(c_3484, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_74])).
% 5.75/2.24  tff(c_3858, plain, (![B_414, C_415]: (k1_relset_1('#skF_1', B_414, C_415)='#skF_1' | ~v1_funct_2(C_415, '#skF_1', B_414) | ~m1_subset_1(C_415, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3455, c_3455, c_3455, c_3455, c_79])).
% 5.75/2.24  tff(c_3863, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_3484, c_3858])).
% 5.75/2.24  tff(c_3870, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3538, c_3676, c_3863])).
% 5.75/2.24  tff(c_3720, plain, (k10_relat_1('#skF_1', '#skF_2')=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3706, c_18])).
% 5.75/2.24  tff(c_3726, plain, (k10_relat_1('#skF_1', '#skF_2')=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3481, c_3720])).
% 5.75/2.24  tff(c_3871, plain, (k10_relat_1('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3870, c_3726])).
% 5.75/2.24  tff(c_4221, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4212])).
% 5.75/2.24  tff(c_4226, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k10_relat_1('#skF_1', '#skF_2') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4221, c_26])).
% 5.75/2.24  tff(c_4233, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3481, c_3454, c_3485, c_3871, c_4226])).
% 5.75/2.24  tff(c_4256, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4233, c_60])).
% 5.75/2.24  tff(c_4282, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4222, c_3480, c_3494, c_4256])).
% 5.75/2.24  tff(c_4284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3495, c_4282])).
% 5.75/2.24  tff(c_4286, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_174])).
% 5.75/2.24  tff(c_4367, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4346, c_4304, c_4286])).
% 5.75/2.24  tff(c_4388, plain, (![C_452]: (v1_xboole_0(C_452) | ~m1_subset_1(C_452, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3455, c_201])).
% 5.75/2.24  tff(c_4398, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_4367, c_4388])).
% 5.75/2.24  tff(c_4294, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3447, c_4])).
% 5.75/2.24  tff(c_4324, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_4294])).
% 5.75/2.24  tff(c_4405, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4398, c_4324])).
% 5.75/2.24  tff(c_4285, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_174])).
% 5.75/2.24  tff(c_4309, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_4285])).
% 5.75/2.24  tff(c_4409, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4405, c_4309])).
% 5.75/2.24  tff(c_4434, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_4430, c_4409])).
% 5.75/2.24  tff(c_4450, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4434, c_4409])).
% 5.75/2.24  tff(c_4315, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_74])).
% 5.75/2.24  tff(c_4452, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4434, c_4315])).
% 5.75/2.24  tff(c_4462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4450, c_4452])).
% 5.75/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.24  
% 5.75/2.24  Inference rules
% 5.75/2.24  ----------------------
% 5.75/2.24  #Ref     : 0
% 5.75/2.24  #Sup     : 939
% 5.75/2.24  #Fact    : 0
% 5.75/2.24  #Define  : 0
% 5.75/2.24  #Split   : 20
% 5.75/2.24  #Chain   : 0
% 5.75/2.24  #Close   : 0
% 5.75/2.24  
% 5.75/2.24  Ordering : KBO
% 5.75/2.24  
% 5.75/2.24  Simplification rules
% 5.75/2.24  ----------------------
% 5.75/2.24  #Subsume      : 86
% 5.75/2.24  #Demod        : 1155
% 5.75/2.24  #Tautology    : 556
% 5.75/2.24  #SimpNegUnit  : 14
% 5.75/2.24  #BackRed      : 167
% 5.75/2.24  
% 5.75/2.24  #Partial instantiations: 0
% 5.75/2.24  #Strategies tried      : 1
% 5.75/2.24  
% 5.75/2.24  Timing (in seconds)
% 5.75/2.24  ----------------------
% 5.75/2.24  Preprocessing        : 0.40
% 5.75/2.24  Parsing              : 0.21
% 5.75/2.24  CNF conversion       : 0.03
% 5.75/2.24  Main loop            : 0.99
% 5.75/2.24  Inferencing          : 0.36
% 5.75/2.24  Reduction            : 0.34
% 5.75/2.24  Demodulation         : 0.24
% 5.75/2.24  BG Simplification    : 0.04
% 5.75/2.24  Subsumption          : 0.16
% 5.75/2.24  Abstraction          : 0.05
% 5.75/2.24  MUC search           : 0.00
% 5.75/2.24  Cooper               : 0.00
% 5.75/2.25  Total                : 1.49
% 5.75/2.25  Index Insertion      : 0.00
% 5.75/2.25  Index Deletion       : 0.00
% 5.75/2.25  Index Matching       : 0.00
% 5.75/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
