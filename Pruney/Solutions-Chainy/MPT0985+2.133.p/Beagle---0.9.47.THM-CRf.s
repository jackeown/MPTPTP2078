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
% DateTime   : Thu Dec  3 10:12:48 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 861 expanded)
%              Number of leaves         :   31 ( 293 expanded)
%              Depth                    :   13
%              Number of atoms          :  313 (2429 expanded)
%              Number of equality atoms :  127 ( 730 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1218,plain,(
    ! [C_164,A_165,B_166] :
      ( v1_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1234,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1218])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1350,plain,(
    ! [A_183,B_184,C_185] :
      ( k2_relset_1(A_183,B_184,C_185) = k2_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1359,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1350])).

tff(c_1373,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1359])).

tff(c_22,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_93,plain,(
    ! [A_27] :
      ( v1_funct_1(k2_funct_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_92,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_96,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_92])).

tff(c_99,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_96])).

tff(c_122,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_122])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_125])).

tff(c_138,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_140,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_164,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_176,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_164])).

tff(c_247,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relset_1(A_57,B_58,C_59) = k2_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_250,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_247])).

tff(c_262,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_250])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_relat_1(A_7) != k1_xboole_0
      | k1_xboole_0 = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_184,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_176,c_12])).

tff(c_196,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_264,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_196])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_341,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_363,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_341])).

tff(c_523,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_xboole_0 = B_90
      | k1_relset_1(A_91,B_90,C_92) = A_91
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_532,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_523])).

tff(c_550,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_363,c_532])).

tff(c_551,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_550])).

tff(c_20,plain,(
    ! [A_9] :
      ( k2_relat_1(k2_funct_1(A_9)) = k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_139,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_215,plain,(
    ! [A_53] :
      ( k2_relat_1(k2_funct_1(A_53)) = k1_relat_1(A_53)
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    ! [A_22] :
      ( v1_funct_2(A_22,k1_relat_1(A_22),k2_relat_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_644,plain,(
    ! [A_99] :
      ( v1_funct_2(k2_funct_1(A_99),k1_relat_1(k2_funct_1(A_99)),k1_relat_1(A_99))
      | ~ v1_funct_1(k2_funct_1(A_99))
      | ~ v1_relat_1(k2_funct_1(A_99))
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_44])).

tff(c_647,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_644])).

tff(c_655,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_58,c_52,c_139,c_647])).

tff(c_656,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_659,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_656])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_58,c_659])).

tff(c_665,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_288,plain,(
    ! [A_64] :
      ( m1_subset_1(A_64,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_64),k2_relat_1(A_64))))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_708,plain,(
    ! [A_101] :
      ( m1_subset_1(k2_funct_1(A_101),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_101),k2_relat_1(k2_funct_1(A_101)))))
      | ~ v1_funct_1(k2_funct_1(A_101))
      | ~ v1_relat_1(k2_funct_1(A_101))
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_288])).

tff(c_728,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_708])).

tff(c_742,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_58,c_52,c_665,c_139,c_728])).

tff(c_762,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_742])).

tff(c_776,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_58,c_52,c_551,c_762])).

tff(c_778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_776])).

tff(c_779,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_788,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_8])).

tff(c_780,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_798,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_780])).

tff(c_142,plain,(
    ! [A_37] :
      ( k1_relat_1(A_37) != k1_xboole_0
      | k1_xboole_0 = A_37
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,(
    ! [A_8] :
      ( k1_relat_1(k2_funct_1(A_8)) != k1_xboole_0
      | k2_funct_1(A_8) = k1_xboole_0
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_142])).

tff(c_962,plain,(
    ! [A_130] :
      ( k1_relat_1(k2_funct_1(A_130)) != '#skF_3'
      | k2_funct_1(A_130) = '#skF_3'
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_779,c_146])).

tff(c_1181,plain,(
    ! [A_157] :
      ( k2_relat_1(A_157) != '#skF_3'
      | k2_funct_1(A_157) = '#skF_3'
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157)
      | ~ v2_funct_1(A_157)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_962])).

tff(c_1184,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1181])).

tff(c_1187,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_58,c_798,c_1184])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_787,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_779,c_6])).

tff(c_916,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_926,plain,(
    ! [A_120,B_121] : k2_relset_1(A_120,B_121,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_788,c_916])).

tff(c_928,plain,(
    ! [A_120,B_121] : k2_relset_1(A_120,B_121,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_926])).

tff(c_929,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_50])).

tff(c_937,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_140])).

tff(c_939,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_937])).

tff(c_1188,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_939])).

tff(c_1192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_1188])).

tff(c_1193,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1243,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1234,c_12])).

tff(c_1264,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1243])).

tff(c_1375,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_1264])).

tff(c_1419,plain,(
    ! [A_189,B_190,C_191] :
      ( k1_relset_1(A_189,B_190,C_191) = k1_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1445,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1419])).

tff(c_1565,plain,(
    ! [B_206,A_207,C_208] :
      ( k1_xboole_0 = B_206
      | k1_relset_1(A_207,B_206,C_208) = A_207
      | ~ v1_funct_2(C_208,A_207,B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1577,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1565])).

tff(c_1597,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1445,c_1577])).

tff(c_1598,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1375,c_1597])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) != k1_xboole_0
      | k1_xboole_0 = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1242,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1234,c_14])).

tff(c_1263,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1242])).

tff(c_1608,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_1263])).

tff(c_1194,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1444,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1194,c_1419])).

tff(c_1682,plain,(
    ! [B_215,C_216,A_217] :
      ( k1_xboole_0 = B_215
      | v1_funct_2(C_216,A_217,B_215)
      | k1_relset_1(A_217,B_215,C_216) != A_217
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_217,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1688,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1194,c_1682])).

tff(c_1704,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_1688])).

tff(c_1705,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1193,c_1608,c_1704])).

tff(c_1715,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1705])).

tff(c_1718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_58,c_52,c_1373,c_1715])).

tff(c_1719,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1243])).

tff(c_1721,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1719,c_1263])).

tff(c_1720,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1243])).

tff(c_1735,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1719,c_1720])).

tff(c_1233,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1194,c_1218])).

tff(c_1260,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0
    | k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1233,c_14])).

tff(c_1813,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1719,c_1719,c_1260])).

tff(c_1814,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1813])).

tff(c_1817,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1814])).

tff(c_1820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_58,c_52,c_1735,c_1817])).

tff(c_1821,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1813])).

tff(c_1835,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1821,c_22])).

tff(c_1845,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_58,c_52,c_1735,c_1835])).

tff(c_1847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1721,c_1845])).

tff(c_1848,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_1849,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_1863,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_1849])).

tff(c_1857,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_8])).

tff(c_2137,plain,(
    ! [A_255,B_256,C_257] :
      ( k1_relset_1(A_255,B_256,C_257) = k1_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2144,plain,(
    ! [A_255,B_256] : k1_relset_1(A_255,B_256,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1857,c_2137])).

tff(c_2153,plain,(
    ! [A_255,B_256] : k1_relset_1(A_255,B_256,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_2144])).

tff(c_34,plain,(
    ! [C_21,B_20] :
      ( v1_funct_2(C_21,k1_xboole_0,B_20)
      | k1_relset_1(k1_xboole_0,B_20,C_21) != k1_xboole_0
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,(
    ! [C_21,B_20] :
      ( v1_funct_2(C_21,k1_xboole_0,B_20)
      | k1_relset_1(k1_xboole_0,B_20,C_21) != k1_xboole_0
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34])).

tff(c_2325,plain,(
    ! [C_279,B_280] :
      ( v1_funct_2(C_279,'#skF_3',B_280)
      | k1_relset_1('#skF_3',B_280,C_279) != '#skF_3'
      | ~ m1_subset_1(C_279,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_1848,c_1848,c_1848,c_62])).

tff(c_2328,plain,(
    ! [B_280] :
      ( v1_funct_2('#skF_3','#skF_3',B_280)
      | k1_relset_1('#skF_3',B_280,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1857,c_2325])).

tff(c_2331,plain,(
    ! [B_280] : v1_funct_2('#skF_3','#skF_3',B_280) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2153,c_2328])).

tff(c_1981,plain,(
    ! [A_246] :
      ( k2_relat_1(k2_funct_1(A_246)) = k1_relat_1(A_246)
      | ~ v2_funct_1(A_246)
      | ~ v1_funct_1(A_246)
      | ~ v1_relat_1(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1261,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0
    | k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1233,c_12])).

tff(c_1942,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_1848,c_1261])).

tff(c_1943,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1942])).

tff(c_1987,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_1943])).

tff(c_1997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_58,c_52,c_1863,c_1987])).

tff(c_1998,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1942])).

tff(c_2010,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1998,c_22])).

tff(c_2020,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_58,c_52,c_1863,c_2010])).

tff(c_2161,plain,(
    ! [A_260,B_261,C_262] :
      ( k2_relset_1(A_260,B_261,C_262) = k2_relat_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2168,plain,(
    ! [A_260,B_261] : k2_relset_1(A_260,B_261,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1857,c_2161])).

tff(c_2177,plain,(
    ! [A_260,B_261] : k2_relset_1(A_260,B_261,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_2168])).

tff(c_2178,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2177,c_50])).

tff(c_2002,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1998,c_1193])).

tff(c_2186,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2178,c_2002])).

tff(c_2354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2331,c_2186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:16:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.69  
% 4.06/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.69  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.06/1.69  
% 4.06/1.69  %Foreground sorts:
% 4.06/1.69  
% 4.06/1.69  
% 4.06/1.69  %Background operators:
% 4.06/1.69  
% 4.06/1.69  
% 4.06/1.69  %Foreground operators:
% 4.06/1.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.06/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.06/1.69  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.06/1.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.06/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.06/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.06/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.06/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.06/1.69  tff('#skF_1', type, '#skF_1': $i).
% 4.06/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.06/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.06/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.06/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.06/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.69  
% 4.06/1.72  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.06/1.72  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.06/1.72  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.06/1.72  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.06/1.72  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.06/1.72  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.06/1.72  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.06/1.72  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.06/1.72  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.06/1.72  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.06/1.72  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.06/1.72  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.06/1.72  tff(c_1218, plain, (![C_164, A_165, B_166]: (v1_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.06/1.72  tff(c_1234, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1218])).
% 4.06/1.72  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.06/1.72  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.06/1.72  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.06/1.72  tff(c_1350, plain, (![A_183, B_184, C_185]: (k2_relset_1(A_183, B_184, C_185)=k2_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.06/1.72  tff(c_1359, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1350])).
% 4.06/1.72  tff(c_1373, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1359])).
% 4.06/1.72  tff(c_22, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.06/1.72  tff(c_93, plain, (![A_27]: (v1_funct_1(k2_funct_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.06/1.72  tff(c_48, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.06/1.72  tff(c_92, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.06/1.72  tff(c_96, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_92])).
% 4.06/1.72  tff(c_99, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_96])).
% 4.06/1.72  tff(c_122, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.06/1.72  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_122])).
% 4.06/1.72  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_125])).
% 4.06/1.72  tff(c_138, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_48])).
% 4.06/1.72  tff(c_140, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_138])).
% 4.06/1.72  tff(c_164, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.06/1.72  tff(c_176, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_164])).
% 4.06/1.72  tff(c_247, plain, (![A_57, B_58, C_59]: (k2_relset_1(A_57, B_58, C_59)=k2_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.06/1.72  tff(c_250, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_247])).
% 4.06/1.72  tff(c_262, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_250])).
% 4.06/1.72  tff(c_12, plain, (![A_7]: (k2_relat_1(A_7)!=k1_xboole_0 | k1_xboole_0=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.06/1.72  tff(c_184, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_176, c_12])).
% 4.06/1.72  tff(c_196, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_184])).
% 4.06/1.72  tff(c_264, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_262, c_196])).
% 4.06/1.72  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.06/1.72  tff(c_341, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.06/1.72  tff(c_363, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_341])).
% 4.06/1.72  tff(c_523, plain, (![B_90, A_91, C_92]: (k1_xboole_0=B_90 | k1_relset_1(A_91, B_90, C_92)=A_91 | ~v1_funct_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.72  tff(c_532, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_523])).
% 4.06/1.72  tff(c_550, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_363, c_532])).
% 4.06/1.72  tff(c_551, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_264, c_550])).
% 4.06/1.72  tff(c_20, plain, (![A_9]: (k2_relat_1(k2_funct_1(A_9))=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.06/1.72  tff(c_18, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.06/1.72  tff(c_139, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 4.06/1.72  tff(c_215, plain, (![A_53]: (k2_relat_1(k2_funct_1(A_53))=k1_relat_1(A_53) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.06/1.72  tff(c_44, plain, (![A_22]: (v1_funct_2(A_22, k1_relat_1(A_22), k2_relat_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.06/1.72  tff(c_644, plain, (![A_99]: (v1_funct_2(k2_funct_1(A_99), k1_relat_1(k2_funct_1(A_99)), k1_relat_1(A_99)) | ~v1_funct_1(k2_funct_1(A_99)) | ~v1_relat_1(k2_funct_1(A_99)) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_215, c_44])).
% 4.06/1.72  tff(c_647, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_551, c_644])).
% 4.06/1.72  tff(c_655, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_58, c_52, c_139, c_647])).
% 4.06/1.72  tff(c_656, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_655])).
% 4.06/1.72  tff(c_659, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_656])).
% 4.06/1.72  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_58, c_659])).
% 4.06/1.72  tff(c_665, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_655])).
% 4.06/1.72  tff(c_288, plain, (![A_64]: (m1_subset_1(A_64, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_64), k2_relat_1(A_64)))) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.06/1.72  tff(c_708, plain, (![A_101]: (m1_subset_1(k2_funct_1(A_101), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_101), k2_relat_1(k2_funct_1(A_101))))) | ~v1_funct_1(k2_funct_1(A_101)) | ~v1_relat_1(k2_funct_1(A_101)) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_22, c_288])).
% 4.06/1.72  tff(c_728, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_262, c_708])).
% 4.06/1.72  tff(c_742, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_58, c_52, c_665, c_139, c_728])).
% 4.06/1.72  tff(c_762, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_742])).
% 4.06/1.72  tff(c_776, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_58, c_52, c_551, c_762])).
% 4.06/1.72  tff(c_778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_776])).
% 4.06/1.72  tff(c_779, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_184])).
% 4.06/1.72  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.06/1.72  tff(c_788, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_779, c_8])).
% 4.06/1.72  tff(c_780, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_184])).
% 4.06/1.72  tff(c_798, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_779, c_780])).
% 4.06/1.72  tff(c_142, plain, (![A_37]: (k1_relat_1(A_37)!=k1_xboole_0 | k1_xboole_0=A_37 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.06/1.72  tff(c_146, plain, (![A_8]: (k1_relat_1(k2_funct_1(A_8))!=k1_xboole_0 | k2_funct_1(A_8)=k1_xboole_0 | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_18, c_142])).
% 4.06/1.72  tff(c_962, plain, (![A_130]: (k1_relat_1(k2_funct_1(A_130))!='#skF_3' | k2_funct_1(A_130)='#skF_3' | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_779, c_779, c_146])).
% 4.06/1.72  tff(c_1181, plain, (![A_157]: (k2_relat_1(A_157)!='#skF_3' | k2_funct_1(A_157)='#skF_3' | ~v1_funct_1(A_157) | ~v1_relat_1(A_157) | ~v2_funct_1(A_157) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(superposition, [status(thm), theory('equality')], [c_22, c_962])).
% 4.06/1.72  tff(c_1184, plain, (k2_relat_1('#skF_3')!='#skF_3' | k2_funct_1('#skF_3')='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1181])).
% 4.06/1.72  tff(c_1187, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_58, c_798, c_1184])).
% 4.06/1.72  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.06/1.72  tff(c_787, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_779, c_779, c_6])).
% 4.06/1.72  tff(c_916, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.06/1.72  tff(c_926, plain, (![A_120, B_121]: (k2_relset_1(A_120, B_121, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_788, c_916])).
% 4.06/1.72  tff(c_928, plain, (![A_120, B_121]: (k2_relset_1(A_120, B_121, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_798, c_926])).
% 4.06/1.72  tff(c_929, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_928, c_50])).
% 4.06/1.72  tff(c_937, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_929, c_140])).
% 4.06/1.72  tff(c_939, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_937])).
% 4.06/1.72  tff(c_1188, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_939])).
% 4.06/1.72  tff(c_1192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_788, c_1188])).
% 4.06/1.72  tff(c_1193, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_138])).
% 4.06/1.72  tff(c_1243, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1234, c_12])).
% 4.06/1.72  tff(c_1264, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1243])).
% 4.06/1.72  tff(c_1375, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1373, c_1264])).
% 4.06/1.72  tff(c_1419, plain, (![A_189, B_190, C_191]: (k1_relset_1(A_189, B_190, C_191)=k1_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.06/1.72  tff(c_1445, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1419])).
% 4.06/1.72  tff(c_1565, plain, (![B_206, A_207, C_208]: (k1_xboole_0=B_206 | k1_relset_1(A_207, B_206, C_208)=A_207 | ~v1_funct_2(C_208, A_207, B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.72  tff(c_1577, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_1565])).
% 4.06/1.72  tff(c_1597, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1445, c_1577])).
% 4.06/1.72  tff(c_1598, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1375, c_1597])).
% 4.06/1.72  tff(c_14, plain, (![A_7]: (k1_relat_1(A_7)!=k1_xboole_0 | k1_xboole_0=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.06/1.72  tff(c_1242, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1234, c_14])).
% 4.06/1.72  tff(c_1263, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1242])).
% 4.06/1.72  tff(c_1608, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1598, c_1263])).
% 4.06/1.72  tff(c_1194, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_138])).
% 4.06/1.72  tff(c_1444, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1194, c_1419])).
% 4.06/1.72  tff(c_1682, plain, (![B_215, C_216, A_217]: (k1_xboole_0=B_215 | v1_funct_2(C_216, A_217, B_215) | k1_relset_1(A_217, B_215, C_216)!=A_217 | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_217, B_215))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.72  tff(c_1688, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1194, c_1682])).
% 4.06/1.72  tff(c_1704, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_1688])).
% 4.06/1.72  tff(c_1705, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1193, c_1608, c_1704])).
% 4.06/1.72  tff(c_1715, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1705])).
% 4.06/1.72  tff(c_1718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1234, c_58, c_52, c_1373, c_1715])).
% 4.06/1.72  tff(c_1719, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1243])).
% 4.06/1.72  tff(c_1721, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1719, c_1263])).
% 4.06/1.72  tff(c_1720, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1243])).
% 4.06/1.72  tff(c_1735, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1719, c_1720])).
% 4.06/1.72  tff(c_1233, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1194, c_1218])).
% 4.06/1.72  tff(c_1260, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0 | k2_funct_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1233, c_14])).
% 4.06/1.72  tff(c_1813, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1719, c_1719, c_1260])).
% 4.06/1.72  tff(c_1814, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1813])).
% 4.06/1.72  tff(c_1817, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1814])).
% 4.06/1.72  tff(c_1820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1234, c_58, c_52, c_1735, c_1817])).
% 4.06/1.72  tff(c_1821, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1813])).
% 4.06/1.72  tff(c_1835, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1821, c_22])).
% 4.06/1.72  tff(c_1845, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_58, c_52, c_1735, c_1835])).
% 4.06/1.72  tff(c_1847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1721, c_1845])).
% 4.06/1.72  tff(c_1848, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1242])).
% 4.06/1.72  tff(c_1849, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1242])).
% 4.06/1.72  tff(c_1863, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_1849])).
% 4.06/1.72  tff(c_1857, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_8])).
% 4.06/1.72  tff(c_2137, plain, (![A_255, B_256, C_257]: (k1_relset_1(A_255, B_256, C_257)=k1_relat_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.06/1.72  tff(c_2144, plain, (![A_255, B_256]: (k1_relset_1(A_255, B_256, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1857, c_2137])).
% 4.06/1.72  tff(c_2153, plain, (![A_255, B_256]: (k1_relset_1(A_255, B_256, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_2144])).
% 4.06/1.72  tff(c_34, plain, (![C_21, B_20]: (v1_funct_2(C_21, k1_xboole_0, B_20) | k1_relset_1(k1_xboole_0, B_20, C_21)!=k1_xboole_0 | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.72  tff(c_62, plain, (![C_21, B_20]: (v1_funct_2(C_21, k1_xboole_0, B_20) | k1_relset_1(k1_xboole_0, B_20, C_21)!=k1_xboole_0 | ~m1_subset_1(C_21, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_34])).
% 4.06/1.72  tff(c_2325, plain, (![C_279, B_280]: (v1_funct_2(C_279, '#skF_3', B_280) | k1_relset_1('#skF_3', B_280, C_279)!='#skF_3' | ~m1_subset_1(C_279, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_1848, c_1848, c_1848, c_62])).
% 4.06/1.72  tff(c_2328, plain, (![B_280]: (v1_funct_2('#skF_3', '#skF_3', B_280) | k1_relset_1('#skF_3', B_280, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_1857, c_2325])).
% 4.06/1.72  tff(c_2331, plain, (![B_280]: (v1_funct_2('#skF_3', '#skF_3', B_280))), inference(demodulation, [status(thm), theory('equality')], [c_2153, c_2328])).
% 4.06/1.72  tff(c_1981, plain, (![A_246]: (k2_relat_1(k2_funct_1(A_246))=k1_relat_1(A_246) | ~v2_funct_1(A_246) | ~v1_funct_1(A_246) | ~v1_relat_1(A_246))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.06/1.72  tff(c_1261, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0 | k2_funct_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1233, c_12])).
% 4.06/1.72  tff(c_1942, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_1848, c_1261])).
% 4.06/1.72  tff(c_1943, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1942])).
% 4.06/1.72  tff(c_1987, plain, (k1_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1981, c_1943])).
% 4.06/1.72  tff(c_1997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1234, c_58, c_52, c_1863, c_1987])).
% 4.06/1.72  tff(c_1998, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1942])).
% 4.06/1.72  tff(c_2010, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1998, c_22])).
% 4.06/1.72  tff(c_2020, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_58, c_52, c_1863, c_2010])).
% 4.06/1.72  tff(c_2161, plain, (![A_260, B_261, C_262]: (k2_relset_1(A_260, B_261, C_262)=k2_relat_1(C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.06/1.72  tff(c_2168, plain, (![A_260, B_261]: (k2_relset_1(A_260, B_261, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1857, c_2161])).
% 4.06/1.72  tff(c_2177, plain, (![A_260, B_261]: (k2_relset_1(A_260, B_261, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_2168])).
% 4.06/1.72  tff(c_2178, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2177, c_50])).
% 4.06/1.72  tff(c_2002, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1998, c_1193])).
% 4.06/1.72  tff(c_2186, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2178, c_2002])).
% 4.06/1.72  tff(c_2354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2331, c_2186])).
% 4.06/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.72  
% 4.06/1.72  Inference rules
% 4.06/1.72  ----------------------
% 4.06/1.72  #Ref     : 0
% 4.06/1.72  #Sup     : 484
% 4.06/1.72  #Fact    : 0
% 4.06/1.72  #Define  : 0
% 4.06/1.72  #Split   : 17
% 4.06/1.72  #Chain   : 0
% 4.06/1.72  #Close   : 0
% 4.06/1.72  
% 4.06/1.72  Ordering : KBO
% 4.06/1.72  
% 4.06/1.72  Simplification rules
% 4.06/1.72  ----------------------
% 4.06/1.72  #Subsume      : 54
% 4.06/1.72  #Demod        : 518
% 4.06/1.72  #Tautology    : 278
% 4.06/1.72  #SimpNegUnit  : 17
% 4.06/1.72  #BackRed      : 60
% 4.06/1.72  
% 4.06/1.72  #Partial instantiations: 0
% 4.06/1.72  #Strategies tried      : 1
% 4.06/1.72  
% 4.06/1.72  Timing (in seconds)
% 4.06/1.72  ----------------------
% 4.06/1.72  Preprocessing        : 0.34
% 4.06/1.72  Parsing              : 0.18
% 4.06/1.72  CNF conversion       : 0.02
% 4.06/1.72  Main loop            : 0.62
% 4.06/1.72  Inferencing          : 0.24
% 4.06/1.72  Reduction            : 0.20
% 4.06/1.72  Demodulation         : 0.14
% 4.06/1.72  BG Simplification    : 0.03
% 4.06/1.72  Subsumption          : 0.10
% 4.06/1.72  Abstraction          : 0.03
% 4.06/1.72  MUC search           : 0.00
% 4.06/1.72  Cooper               : 0.00
% 4.06/1.72  Total                : 1.01
% 4.06/1.72  Index Insertion      : 0.00
% 4.06/1.72  Index Deletion       : 0.00
% 4.06/1.72  Index Matching       : 0.00
% 4.06/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
