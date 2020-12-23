%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:41 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  188 (1007 expanded)
%              Number of leaves         :   34 ( 329 expanded)
%              Depth                    :   14
%              Number of atoms          :  333 (2687 expanded)
%              Number of equality atoms :   86 ( 458 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_131,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1145,plain,(
    ! [C_158,A_159,B_160] :
      ( v1_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1157,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1145])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_118,plain,(
    ! [C_47,B_48,A_49] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(B_48,A_49)))
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_126,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_129,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_77,plain,(
    ! [A_36] :
      ( v1_funct_1(k2_funct_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_69,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_80,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_69])).

tff(c_83,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_80])).

tff(c_84,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_87,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_87])).

tff(c_96,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_105,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_107,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_115,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_107])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_202,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_210,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_202])).

tff(c_445,plain,(
    ! [B_91,A_92,C_93] :
      ( k1_xboole_0 = B_91
      | k1_relset_1(A_92,B_91,C_93) = A_92
      | ~ v1_funct_2(C_93,A_92,B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_454,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_445])).

tff(c_465,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_210,c_454])).

tff(c_468,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_14,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_175,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_178,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_175])).

tff(c_184,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_178])).

tff(c_151,plain,(
    ! [A_59] :
      ( k1_relat_1(k2_funct_1(A_59)) = k2_relat_1(A_59)
      | ~ v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_29] :
      ( v1_funct_2(A_29,k1_relat_1(A_29),k2_relat_1(A_29))
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_575,plain,(
    ! [A_100] :
      ( v1_funct_2(k2_funct_1(A_100),k2_relat_1(A_100),k2_relat_1(k2_funct_1(A_100)))
      | ~ v1_funct_1(k2_funct_1(A_100))
      | ~ v1_relat_1(k2_funct_1(A_100))
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_42])).

tff(c_578,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_575])).

tff(c_586,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_56,c_50,c_97,c_578])).

tff(c_587,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_590,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_587])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_56,c_590])).

tff(c_596,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(k2_funct_1(A_8)) = k2_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_223,plain,(
    ! [A_71] :
      ( m1_subset_1(A_71,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71))))
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_616,plain,(
    ! [A_103] :
      ( m1_subset_1(k2_funct_1(A_103),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_103),k2_relat_1(k2_funct_1(A_103)))))
      | ~ v1_funct_1(k2_funct_1(A_103))
      | ~ v1_relat_1(k2_funct_1(A_103))
      | ~ v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_223])).

tff(c_642,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_616])).

tff(c_658,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_56,c_50,c_596,c_97,c_642])).

tff(c_684,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_658])).

tff(c_698,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_56,c_50,c_468,c_684])).

tff(c_700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_698])).

tff(c_701,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_718,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_2])).

tff(c_720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_718])).

tff(c_721,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_65,plain,(
    ! [B_32,A_33] :
      ( ~ v1_xboole_0(B_32)
      | B_32 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [A_33] :
      ( k1_xboole_0 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_2,c_65])).

tff(c_728,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_721,c_68])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_740,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_6])).

tff(c_868,plain,(
    ! [A_125,B_126,C_127] :
      ( k2_relset_1(A_125,B_126,C_127) = k2_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_878,plain,(
    ! [A_128,B_129] : k2_relset_1(A_128,B_129,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_740,c_868])).

tff(c_722,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_735,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_722,c_68])).

tff(c_748,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_735])).

tff(c_752,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_748,c_48])).

tff(c_882,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_752])).

tff(c_821,plain,(
    ! [A_117] :
      ( m1_subset_1(A_117,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_117),k2_relat_1(A_117))))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_xboole_0(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_860,plain,(
    ! [A_123] :
      ( v1_xboole_0(A_123)
      | ~ v1_xboole_0(k1_relat_1(A_123))
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_821,c_20])).

tff(c_1100,plain,(
    ! [A_155] :
      ( v1_xboole_0(k2_funct_1(A_155))
      | ~ v1_xboole_0(k2_relat_1(A_155))
      | ~ v1_funct_1(k2_funct_1(A_155))
      | ~ v1_relat_1(k2_funct_1(A_155))
      | ~ v2_funct_1(A_155)
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_860])).

tff(c_1103,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_1100])).

tff(c_1108,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_56,c_50,c_97,c_721,c_1103])).

tff(c_1109,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1108])).

tff(c_1112,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1109])).

tff(c_1116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_56,c_1112])).

tff(c_1117,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1108])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_729,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_721,c_4])).

tff(c_1124,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1117,c_729])).

tff(c_750,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_105])).

tff(c_1135,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_750])).

tff(c_1141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_1135])).

tff(c_1143,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1173,plain,(
    ! [C_169,B_170,A_171] :
      ( v1_xboole_0(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(B_170,A_171)))
      | ~ v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1184,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1143,c_1173])).

tff(c_1189,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1184])).

tff(c_1258,plain,(
    ! [A_182,B_183,C_184] :
      ( k2_relset_1(A_182,B_183,C_184) = k2_relat_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1264,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1258])).

tff(c_1271,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1264])).

tff(c_1142,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1229,plain,(
    ! [A_177,B_178,C_179] :
      ( k1_relset_1(A_177,B_178,C_179) = k1_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1240,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1143,c_1229])).

tff(c_1514,plain,(
    ! [B_205,C_206,A_207] :
      ( k1_xboole_0 = B_205
      | v1_funct_2(C_206,A_207,B_205)
      | k1_relset_1(A_207,B_205,C_206) != A_207
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1523,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1143,c_1514])).

tff(c_1536,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_1523])).

tff(c_1537,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1142,c_1536])).

tff(c_1591,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1537])).

tff(c_1594,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1591])).

tff(c_1597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_56,c_50,c_1271,c_1594])).

tff(c_1598,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1537])).

tff(c_1614,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_2])).

tff(c_1616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1189,c_1614])).

tff(c_1618,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1184])).

tff(c_1624,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1618,c_68])).

tff(c_28,plain,(
    ! [A_26] :
      ( v1_funct_2(k1_xboole_0,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    ! [A_26] :
      ( v1_funct_2(k1_xboole_0,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_1791,plain,(
    ! [A_217] :
      ( v1_funct_2('#skF_1',A_217,'#skF_1')
      | A_217 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1624,c_1624,c_58])).

tff(c_1637,plain,(
    ! [C_208,A_209,B_210] :
      ( v1_xboole_0(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_xboole_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1643,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1637])).

tff(c_1647,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1643])).

tff(c_1654,plain,(
    ! [A_211] :
      ( A_211 = '#skF_1'
      | ~ v1_xboole_0(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_68])).

tff(c_1665,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1647,c_1654])).

tff(c_1617,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1184])).

tff(c_1664,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1617,c_1654])).

tff(c_1695,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1664])).

tff(c_1675,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_1142])).

tff(c_1787,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1675])).

tff(c_1795,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1791,c_1787])).

tff(c_1185,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1173])).

tff(c_1188,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1185])).

tff(c_1799,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1795,c_1188])).

tff(c_1802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1799])).

tff(c_1804,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1185])).

tff(c_1831,plain,(
    ! [C_218,A_219,B_220] :
      ( v1_xboole_0(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ v1_xboole_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1834,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1143,c_1831])).

tff(c_1840,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_1834])).

tff(c_1803,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1185])).

tff(c_1810,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1803,c_68])).

tff(c_1817,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1804,c_68])).

tff(c_1843,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_1817])).

tff(c_1818,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1804,c_4])).

tff(c_1861,plain,(
    ! [A_221] :
      ( A_221 = '#skF_3'
      | ~ v1_xboole_0(A_221) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_1818])).

tff(c_1868,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1840,c_1861])).

tff(c_1914,plain,(
    ! [A_223] :
      ( k2_relat_1(k2_funct_1(A_223)) = k1_relat_1(A_223)
      | ~ v2_funct_1(A_223)
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1926,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1868,c_1914])).

tff(c_1930,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_56,c_50,c_1926])).

tff(c_1823,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_6])).

tff(c_2025,plain,(
    ! [A_236,B_237,C_238] :
      ( k2_relset_1(A_236,B_237,C_238) = k2_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2032,plain,(
    ! [A_236,B_237] : k2_relset_1(A_236,B_237,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1823,c_2025])).

tff(c_2044,plain,(
    ! [A_241,B_242] : k2_relset_1(A_241,B_242,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_2032])).

tff(c_1850,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_1843,c_48])).

tff(c_2048,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_1850])).

tff(c_1968,plain,(
    ! [A_228,B_229,C_230] :
      ( k1_relset_1(A_228,B_229,C_230) = k1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1973,plain,(
    ! [A_228,B_229] : k1_relset_1(A_228,B_229,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1823,c_1968])).

tff(c_2056,plain,(
    ! [A_228,B_229] : k1_relset_1(A_228,B_229,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_1973])).

tff(c_32,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2109,plain,(
    ! [C_245,B_246] :
      ( v1_funct_2(C_245,'#skF_3',B_246)
      | k1_relset_1('#skF_3',B_246,C_245) != '#skF_3'
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_246))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_1810,c_1810,c_1810,c_32])).

tff(c_2113,plain,(
    ! [B_246] :
      ( v1_funct_2('#skF_3','#skF_3',B_246)
      | k1_relset_1('#skF_3',B_246,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1823,c_2109])).

tff(c_2116,plain,(
    ! [B_246] : v1_funct_2('#skF_3','#skF_3',B_246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_2113])).

tff(c_1848,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_1142])).

tff(c_1946,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1868,c_1848])).

tff(c_2120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_1946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.68  
% 3.96/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.68  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.96/1.68  
% 3.96/1.68  %Foreground sorts:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Background operators:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Foreground operators:
% 3.96/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.96/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.96/1.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.96/1.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.96/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.96/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.96/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.96/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.68  
% 3.96/1.71  tff(f_131, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.96/1.71  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.96/1.71  tff(f_78, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.96/1.71  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.96/1.71  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.96/1.71  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.96/1.71  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.96/1.71  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.96/1.71  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.96/1.71  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.96/1.71  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.96/1.71  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.96/1.71  tff(f_71, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.96/1.71  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.96/1.71  tff(c_1145, plain, (![C_158, A_159, B_160]: (v1_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.96/1.71  tff(c_1157, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1145])).
% 3.96/1.71  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.96/1.71  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.96/1.71  tff(c_118, plain, (![C_47, B_48, A_49]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(B_48, A_49))) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.96/1.71  tff(c_126, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_118])).
% 3.96/1.71  tff(c_129, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_126])).
% 3.96/1.71  tff(c_77, plain, (![A_36]: (v1_funct_1(k2_funct_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.96/1.71  tff(c_46, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.96/1.71  tff(c_69, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.96/1.71  tff(c_80, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_77, c_69])).
% 3.96/1.71  tff(c_83, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_80])).
% 3.96/1.71  tff(c_84, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.96/1.71  tff(c_87, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_84])).
% 3.96/1.71  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_87])).
% 3.96/1.71  tff(c_96, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_46])).
% 3.96/1.71  tff(c_105, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_96])).
% 3.96/1.71  tff(c_107, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.96/1.71  tff(c_115, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_107])).
% 3.96/1.71  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.96/1.71  tff(c_202, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.96/1.71  tff(c_210, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_202])).
% 3.96/1.71  tff(c_445, plain, (![B_91, A_92, C_93]: (k1_xboole_0=B_91 | k1_relset_1(A_92, B_91, C_93)=A_92 | ~v1_funct_2(C_93, A_92, B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.96/1.71  tff(c_454, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_445])).
% 3.96/1.71  tff(c_465, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_210, c_454])).
% 3.96/1.71  tff(c_468, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_465])).
% 3.96/1.71  tff(c_14, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.96/1.71  tff(c_12, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.96/1.71  tff(c_97, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 3.96/1.71  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.96/1.71  tff(c_175, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.96/1.71  tff(c_178, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_175])).
% 3.96/1.71  tff(c_184, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_178])).
% 3.96/1.71  tff(c_151, plain, (![A_59]: (k1_relat_1(k2_funct_1(A_59))=k2_relat_1(A_59) | ~v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.96/1.71  tff(c_42, plain, (![A_29]: (v1_funct_2(A_29, k1_relat_1(A_29), k2_relat_1(A_29)) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.71  tff(c_575, plain, (![A_100]: (v1_funct_2(k2_funct_1(A_100), k2_relat_1(A_100), k2_relat_1(k2_funct_1(A_100))) | ~v1_funct_1(k2_funct_1(A_100)) | ~v1_relat_1(k2_funct_1(A_100)) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_151, c_42])).
% 3.96/1.71  tff(c_578, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_184, c_575])).
% 3.96/1.71  tff(c_586, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_56, c_50, c_97, c_578])).
% 3.96/1.71  tff(c_587, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_586])).
% 3.96/1.71  tff(c_590, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_587])).
% 3.96/1.71  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_56, c_590])).
% 3.96/1.71  tff(c_596, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_586])).
% 3.96/1.71  tff(c_16, plain, (![A_8]: (k1_relat_1(k2_funct_1(A_8))=k2_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.96/1.71  tff(c_223, plain, (![A_71]: (m1_subset_1(A_71, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)))) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.71  tff(c_616, plain, (![A_103]: (m1_subset_1(k2_funct_1(A_103), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_103), k2_relat_1(k2_funct_1(A_103))))) | ~v1_funct_1(k2_funct_1(A_103)) | ~v1_relat_1(k2_funct_1(A_103)) | ~v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_16, c_223])).
% 3.96/1.71  tff(c_642, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_184, c_616])).
% 3.96/1.71  tff(c_658, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_56, c_50, c_596, c_97, c_642])).
% 3.96/1.71  tff(c_684, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_658])).
% 3.96/1.71  tff(c_698, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_56, c_50, c_468, c_684])).
% 3.96/1.71  tff(c_700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_698])).
% 3.96/1.71  tff(c_701, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_465])).
% 3.96/1.71  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.96/1.71  tff(c_718, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_701, c_2])).
% 3.96/1.71  tff(c_720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_718])).
% 3.96/1.71  tff(c_721, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_126])).
% 3.96/1.71  tff(c_65, plain, (![B_32, A_33]: (~v1_xboole_0(B_32) | B_32=A_33 | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.96/1.71  tff(c_68, plain, (![A_33]: (k1_xboole_0=A_33 | ~v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_2, c_65])).
% 3.96/1.71  tff(c_728, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_721, c_68])).
% 3.96/1.71  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.96/1.71  tff(c_740, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_728, c_6])).
% 3.96/1.71  tff(c_868, plain, (![A_125, B_126, C_127]: (k2_relset_1(A_125, B_126, C_127)=k2_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.96/1.71  tff(c_878, plain, (![A_128, B_129]: (k2_relset_1(A_128, B_129, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_740, c_868])).
% 3.96/1.71  tff(c_722, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 3.96/1.71  tff(c_735, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_722, c_68])).
% 3.96/1.71  tff(c_748, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_728, c_735])).
% 3.96/1.71  tff(c_752, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_748, c_748, c_48])).
% 3.96/1.71  tff(c_882, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_878, c_752])).
% 3.96/1.71  tff(c_821, plain, (![A_117]: (m1_subset_1(A_117, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_117), k2_relat_1(A_117)))) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.96/1.71  tff(c_20, plain, (![C_15, A_12, B_13]: (v1_xboole_0(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.96/1.71  tff(c_860, plain, (![A_123]: (v1_xboole_0(A_123) | ~v1_xboole_0(k1_relat_1(A_123)) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_821, c_20])).
% 3.96/1.71  tff(c_1100, plain, (![A_155]: (v1_xboole_0(k2_funct_1(A_155)) | ~v1_xboole_0(k2_relat_1(A_155)) | ~v1_funct_1(k2_funct_1(A_155)) | ~v1_relat_1(k2_funct_1(A_155)) | ~v2_funct_1(A_155) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(superposition, [status(thm), theory('equality')], [c_16, c_860])).
% 3.96/1.71  tff(c_1103, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_882, c_1100])).
% 3.96/1.71  tff(c_1108, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_56, c_50, c_97, c_721, c_1103])).
% 3.96/1.71  tff(c_1109, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1108])).
% 3.96/1.71  tff(c_1112, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1109])).
% 3.96/1.71  tff(c_1116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_56, c_1112])).
% 3.96/1.71  tff(c_1117, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1108])).
% 3.96/1.71  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.96/1.71  tff(c_729, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_721, c_4])).
% 3.96/1.71  tff(c_1124, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1117, c_729])).
% 3.96/1.71  tff(c_750, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_748, c_105])).
% 3.96/1.71  tff(c_1135, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_750])).
% 3.96/1.71  tff(c_1141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_740, c_1135])).
% 3.96/1.71  tff(c_1143, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_96])).
% 3.96/1.71  tff(c_1173, plain, (![C_169, B_170, A_171]: (v1_xboole_0(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(B_170, A_171))) | ~v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.96/1.71  tff(c_1184, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1143, c_1173])).
% 3.96/1.71  tff(c_1189, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1184])).
% 3.96/1.71  tff(c_1258, plain, (![A_182, B_183, C_184]: (k2_relset_1(A_182, B_183, C_184)=k2_relat_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.96/1.71  tff(c_1264, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1258])).
% 3.96/1.71  tff(c_1271, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1264])).
% 3.96/1.71  tff(c_1142, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_96])).
% 3.96/1.71  tff(c_1229, plain, (![A_177, B_178, C_179]: (k1_relset_1(A_177, B_178, C_179)=k1_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.96/1.71  tff(c_1240, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1143, c_1229])).
% 3.96/1.71  tff(c_1514, plain, (![B_205, C_206, A_207]: (k1_xboole_0=B_205 | v1_funct_2(C_206, A_207, B_205) | k1_relset_1(A_207, B_205, C_206)!=A_207 | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_205))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.96/1.71  tff(c_1523, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1143, c_1514])).
% 3.96/1.71  tff(c_1536, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_1523])).
% 3.96/1.71  tff(c_1537, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1142, c_1536])).
% 3.96/1.71  tff(c_1591, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1537])).
% 3.96/1.71  tff(c_1594, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1591])).
% 3.96/1.71  tff(c_1597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1157, c_56, c_50, c_1271, c_1594])).
% 3.96/1.71  tff(c_1598, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1537])).
% 3.96/1.71  tff(c_1614, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1598, c_2])).
% 3.96/1.71  tff(c_1616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1189, c_1614])).
% 3.96/1.71  tff(c_1618, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_1184])).
% 3.96/1.71  tff(c_1624, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1618, c_68])).
% 3.96/1.71  tff(c_28, plain, (![A_26]: (v1_funct_2(k1_xboole_0, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.96/1.71  tff(c_58, plain, (![A_26]: (v1_funct_2(k1_xboole_0, A_26, k1_xboole_0) | k1_xboole_0=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 3.96/1.71  tff(c_1791, plain, (![A_217]: (v1_funct_2('#skF_1', A_217, '#skF_1') | A_217='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1624, c_1624, c_58])).
% 3.96/1.71  tff(c_1637, plain, (![C_208, A_209, B_210]: (v1_xboole_0(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_xboole_0(A_209))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.96/1.71  tff(c_1643, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1637])).
% 3.96/1.71  tff(c_1647, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1643])).
% 3.96/1.71  tff(c_1654, plain, (![A_211]: (A_211='#skF_1' | ~v1_xboole_0(A_211))), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_68])).
% 3.96/1.71  tff(c_1665, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_1647, c_1654])).
% 3.96/1.71  tff(c_1617, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1184])).
% 3.96/1.71  tff(c_1664, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_1617, c_1654])).
% 3.96/1.71  tff(c_1695, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1664])).
% 3.96/1.71  tff(c_1675, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_1142])).
% 3.96/1.71  tff(c_1787, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1675])).
% 3.96/1.71  tff(c_1795, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_1791, c_1787])).
% 3.96/1.71  tff(c_1185, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1173])).
% 3.96/1.71  tff(c_1188, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1185])).
% 3.96/1.71  tff(c_1799, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1795, c_1188])).
% 3.96/1.71  tff(c_1802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1799])).
% 3.96/1.71  tff(c_1804, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_1185])).
% 3.96/1.71  tff(c_1831, plain, (![C_218, A_219, B_220]: (v1_xboole_0(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~v1_xboole_0(A_219))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.96/1.71  tff(c_1834, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1143, c_1831])).
% 3.96/1.71  tff(c_1840, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1804, c_1834])).
% 3.96/1.71  tff(c_1803, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1185])).
% 3.96/1.71  tff(c_1810, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1803, c_68])).
% 3.96/1.71  tff(c_1817, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1804, c_68])).
% 3.96/1.71  tff(c_1843, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1810, c_1817])).
% 3.96/1.71  tff(c_1818, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1804, c_4])).
% 3.96/1.71  tff(c_1861, plain, (![A_221]: (A_221='#skF_3' | ~v1_xboole_0(A_221))), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_1818])).
% 3.96/1.71  tff(c_1868, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1840, c_1861])).
% 3.96/1.71  tff(c_1914, plain, (![A_223]: (k2_relat_1(k2_funct_1(A_223))=k1_relat_1(A_223) | ~v2_funct_1(A_223) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.96/1.71  tff(c_1926, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1868, c_1914])).
% 3.96/1.71  tff(c_1930, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1157, c_56, c_50, c_1926])).
% 3.96/1.71  tff(c_1823, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_1810, c_6])).
% 3.96/1.71  tff(c_2025, plain, (![A_236, B_237, C_238]: (k2_relset_1(A_236, B_237, C_238)=k2_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.96/1.71  tff(c_2032, plain, (![A_236, B_237]: (k2_relset_1(A_236, B_237, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1823, c_2025])).
% 3.96/1.71  tff(c_2044, plain, (![A_241, B_242]: (k2_relset_1(A_241, B_242, '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_2032])).
% 3.96/1.71  tff(c_1850, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_1843, c_48])).
% 3.96/1.71  tff(c_2048, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2044, c_1850])).
% 3.96/1.71  tff(c_1968, plain, (![A_228, B_229, C_230]: (k1_relset_1(A_228, B_229, C_230)=k1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.96/1.71  tff(c_1973, plain, (![A_228, B_229]: (k1_relset_1(A_228, B_229, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1823, c_1968])).
% 3.96/1.71  tff(c_2056, plain, (![A_228, B_229]: (k1_relset_1(A_228, B_229, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_1973])).
% 3.96/1.71  tff(c_32, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.96/1.71  tff(c_2109, plain, (![C_245, B_246]: (v1_funct_2(C_245, '#skF_3', B_246) | k1_relset_1('#skF_3', B_246, C_245)!='#skF_3' | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_246))))), inference(demodulation, [status(thm), theory('equality')], [c_1810, c_1810, c_1810, c_1810, c_32])).
% 3.96/1.71  tff(c_2113, plain, (![B_246]: (v1_funct_2('#skF_3', '#skF_3', B_246) | k1_relset_1('#skF_3', B_246, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_1823, c_2109])).
% 3.96/1.71  tff(c_2116, plain, (![B_246]: (v1_funct_2('#skF_3', '#skF_3', B_246))), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_2113])).
% 3.96/1.71  tff(c_1848, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_1142])).
% 3.96/1.71  tff(c_1946, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1868, c_1848])).
% 3.96/1.71  tff(c_2120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2116, c_1946])).
% 3.96/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.71  
% 3.96/1.71  Inference rules
% 3.96/1.71  ----------------------
% 3.96/1.71  #Ref     : 0
% 3.96/1.71  #Sup     : 430
% 3.96/1.71  #Fact    : 0
% 3.96/1.71  #Define  : 0
% 3.96/1.71  #Split   : 16
% 3.96/1.71  #Chain   : 0
% 3.96/1.71  #Close   : 0
% 3.96/1.71  
% 3.96/1.71  Ordering : KBO
% 3.96/1.71  
% 3.96/1.71  Simplification rules
% 3.96/1.71  ----------------------
% 3.96/1.71  #Subsume      : 47
% 3.96/1.71  #Demod        : 506
% 3.96/1.71  #Tautology    : 239
% 3.96/1.71  #SimpNegUnit  : 8
% 3.96/1.71  #BackRed      : 109
% 3.96/1.71  
% 3.96/1.71  #Partial instantiations: 0
% 3.96/1.71  #Strategies tried      : 1
% 3.96/1.71  
% 3.96/1.71  Timing (in seconds)
% 3.96/1.71  ----------------------
% 3.96/1.71  Preprocessing        : 0.33
% 3.96/1.71  Parsing              : 0.18
% 3.96/1.71  CNF conversion       : 0.02
% 3.96/1.71  Main loop            : 0.57
% 3.96/1.71  Inferencing          : 0.21
% 3.96/1.71  Reduction            : 0.19
% 3.96/1.71  Demodulation         : 0.13
% 3.96/1.71  BG Simplification    : 0.03
% 3.96/1.71  Subsumption          : 0.09
% 3.96/1.71  Abstraction          : 0.03
% 3.96/1.71  MUC search           : 0.00
% 3.96/1.71  Cooper               : 0.00
% 3.96/1.71  Total                : 0.96
% 3.96/1.71  Index Insertion      : 0.00
% 3.96/1.71  Index Deletion       : 0.00
% 3.96/1.71  Index Matching       : 0.00
% 3.96/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
