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
% DateTime   : Thu Dec  3 10:12:40 EST 2020

% Result     : Theorem 6.80s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :  215 (1026 expanded)
%              Number of leaves         :   40 ( 355 expanded)
%              Depth                    :   14
%              Number of atoms          :  446 (2888 expanded)
%              Number of equality atoms :  112 ( 735 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_131,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,A)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3366,plain,(
    ! [C_300,A_301,B_302] :
      ( v1_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3379,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3366])).

tff(c_3521,plain,(
    ! [C_319,A_320,B_321] :
      ( v4_relat_1(C_319,A_320)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3534,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_3521])).

tff(c_22,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3402,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3379,c_22])).

tff(c_3420,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3402])).

tff(c_172,plain,(
    ! [A_39] :
      ( v1_funct_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_154,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_175,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_154])).

tff(c_178,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_175])).

tff(c_184,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_191,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_184])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_191])).

tff(c_198,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_32,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_242,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_251,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_242])).

tff(c_344,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_353,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_344])).

tff(c_263,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_251,c_22])).

tff(c_265,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_30,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_518,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_531,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_518])).

tff(c_537,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_531])).

tff(c_394,plain,(
    ! [A_79] :
      ( k1_relat_1(k2_funct_1(A_79)) = k2_relat_1(A_79)
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_54,plain,(
    ! [A_23] :
      ( v1_funct_2(A_23,k1_relat_1(A_23),k2_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1146,plain,(
    ! [A_142] :
      ( v1_funct_2(k2_funct_1(A_142),k2_relat_1(A_142),k2_relat_1(k2_funct_1(A_142)))
      | ~ v1_funct_1(k2_funct_1(A_142))
      | ~ v1_relat_1(k2_funct_1(A_142))
      | ~ v2_funct_1(A_142)
      | ~ v1_funct_1(A_142)
      | ~ v1_relat_1(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_54])).

tff(c_1155,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_1146])).

tff(c_1169,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_80,c_74,c_198,c_1155])).

tff(c_1172,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1169])).

tff(c_1175,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1172])).

tff(c_1179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_80,c_1175])).

tff(c_1180,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1169])).

tff(c_1204,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1180])).

tff(c_1208,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_80,c_74,c_1204])).

tff(c_1181,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1169])).

tff(c_34,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_452,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_89),k2_relat_1(A_89))))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1307,plain,(
    ! [A_148] :
      ( m1_subset_1(k2_funct_1(A_148),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_148),k2_relat_1(k2_funct_1(A_148)))))
      | ~ v1_funct_1(k2_funct_1(A_148))
      | ~ v1_relat_1(k2_funct_1(A_148))
      | ~ v2_funct_1(A_148)
      | ~ v1_funct_1(A_148)
      | ~ v1_relat_1(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_452])).

tff(c_1331,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_1307])).

tff(c_1350,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_80,c_74,c_1181,c_198,c_1331])).

tff(c_1373,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1350])).

tff(c_1383,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_80,c_74,c_1373])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1059,plain,(
    ! [B_126,D_127,A_128,C_129] :
      ( k1_xboole_0 = B_126
      | m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_128,C_129)))
      | ~ r1_tarski(B_126,C_129)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_126)))
      | ~ v1_funct_2(D_127,A_128,B_126)
      | ~ v1_funct_1(D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2471,plain,(
    ! [B_206,D_207,A_208,A_209] :
      ( k1_relat_1(B_206) = k1_xboole_0
      | m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_208,A_209)))
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_208,k1_relat_1(B_206))))
      | ~ v1_funct_2(D_207,A_208,k1_relat_1(B_206))
      | ~ v1_funct_1(D_207)
      | ~ v4_relat_1(B_206,A_209)
      | ~ v1_relat_1(B_206) ) ),
    inference(resolution,[status(thm)],[c_12,c_1059])).

tff(c_2481,plain,(
    ! [A_209] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_209)))
      | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_209)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1383,c_2471])).

tff(c_2498,plain,(
    ! [A_209] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_209)))
      | ~ v4_relat_1('#skF_3',A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_198,c_1208,c_2481])).

tff(c_2503,plain,(
    ! [A_210] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_210)))
      | ~ v4_relat_1('#skF_3',A_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_2498])).

tff(c_197,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_207,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_2532,plain,(
    ~ v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_2503,c_207])).

tff(c_2557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_2532])).

tff(c_2558,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_24,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) = k1_xboole_0
      | k2_relat_1(A_10) != k1_xboole_0
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_261,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_251,c_24])).

tff(c_2581,plain,
    ( k1_relat_1('#skF_3') = '#skF_3'
    | k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_261])).

tff(c_2582,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2581])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_90,plain,(
    ! [A_31] :
      ( v1_xboole_0(k2_relat_1(A_31))
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_99,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) = k1_xboole_0
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_107,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_99])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_227,plain,(
    ! [A_50] :
      ( k1_relat_1(A_50) = k1_xboole_0
      | k2_relat_1(A_50) != k1_xboole_0
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_233,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_227])).

tff(c_237,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_233])).

tff(c_2561,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_237])).

tff(c_26,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) = k1_xboole_0
      | k1_relat_1(A_10) != k1_xboole_0
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2590,plain,(
    ! [A_212] :
      ( k2_relat_1(A_212) = '#skF_3'
      | k1_relat_1(A_212) != '#skF_3'
      | ~ v1_relat_1(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_26])).

tff(c_2593,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | k1_relat_1('#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_251,c_2590])).

tff(c_2599,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2561,c_2593])).

tff(c_2601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2582,c_2599])).

tff(c_2603,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2581])).

tff(c_20,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_262,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_251,c_20])).

tff(c_264,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_2560,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_264])).

tff(c_2623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_2560])).

tff(c_2624,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_16,plain,(
    ! [A_7] : v4_relat_1(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2651,plain,(
    ! [A_7] : v4_relat_1('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2624,c_16])).

tff(c_2642,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2624,c_2624,c_237])).

tff(c_2680,plain,(
    ! [B_218,A_219] :
      ( r1_tarski(k1_relat_1(B_218),A_219)
      | ~ v4_relat_1(B_218,A_219)
      | ~ v1_relat_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2683,plain,(
    ! [A_219] :
      ( r1_tarski('#skF_3',A_219)
      | ~ v4_relat_1('#skF_3',A_219)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2642,c_2680])).

tff(c_2685,plain,(
    ! [A_219] : r1_tarski('#skF_3',A_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_2651,c_2683])).

tff(c_2625,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_2663,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2624,c_2625])).

tff(c_208,plain,(
    ! [A_46] :
      ( v1_relat_1(k2_funct_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_216,plain,(
    ! [A_46] :
      ( k1_relat_1(k2_funct_1(A_46)) != k1_xboole_0
      | k2_funct_1(A_46) = k1_xboole_0
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_208,c_22])).

tff(c_2912,plain,(
    ! [A_251] :
      ( k1_relat_1(k2_funct_1(A_251)) != '#skF_3'
      | k2_funct_1(A_251) = '#skF_3'
      | ~ v1_funct_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2624,c_2624,c_216])).

tff(c_3332,plain,(
    ! [A_295] :
      ( k2_relat_1(A_295) != '#skF_3'
      | k2_funct_1(A_295) = '#skF_3'
      | ~ v1_funct_1(A_295)
      | ~ v1_relat_1(A_295)
      | ~ v2_funct_1(A_295)
      | ~ v1_funct_1(A_295)
      | ~ v1_relat_1(A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2912])).

tff(c_3335,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3332])).

tff(c_3338,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_80,c_2663,c_3335])).

tff(c_2935,plain,(
    ! [A_259,B_260,C_261] :
      ( k2_relset_1(A_259,B_260,C_261) = k2_relat_1(C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2942,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2935])).

tff(c_2945,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2663,c_72,c_2942])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_226,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_2946,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2945,c_226])).

tff(c_3340,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3338,c_2946])).

tff(c_3344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_3340])).

tff(c_3346,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_3378,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3346,c_3366])).

tff(c_3626,plain,(
    ! [A_331,B_332,C_333] :
      ( k2_relset_1(A_331,B_332,C_333) = k2_relat_1(C_333)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3636,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3626])).

tff(c_3640,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3636])).

tff(c_3571,plain,(
    ! [A_326] :
      ( k1_relat_1(k2_funct_1(A_326)) = k2_relat_1(A_326)
      | ~ v2_funct_1(A_326)
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4664,plain,(
    ! [A_403] :
      ( v1_funct_2(k2_funct_1(A_403),k2_relat_1(A_403),k2_relat_1(k2_funct_1(A_403)))
      | ~ v1_funct_1(k2_funct_1(A_403))
      | ~ v1_relat_1(k2_funct_1(A_403))
      | ~ v2_funct_1(A_403)
      | ~ v1_funct_1(A_403)
      | ~ v1_relat_1(A_403) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3571,c_54])).

tff(c_4673,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_4664])).

tff(c_4687,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_80,c_74,c_3378,c_198,c_4673])).

tff(c_4695,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4687])).

tff(c_4699,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_80,c_74,c_4695])).

tff(c_3658,plain,(
    ! [A_334] :
      ( m1_subset_1(A_334,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_334),k2_relat_1(A_334))))
      | ~ v1_funct_1(A_334)
      | ~ v1_relat_1(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5127,plain,(
    ! [A_424] :
      ( m1_subset_1(k2_funct_1(A_424),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_424),k2_relat_1(k2_funct_1(A_424)))))
      | ~ v1_funct_1(k2_funct_1(A_424))
      | ~ v1_relat_1(k2_funct_1(A_424))
      | ~ v2_funct_1(A_424)
      | ~ v1_funct_1(A_424)
      | ~ v1_relat_1(A_424) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3658])).

tff(c_5151,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_5127])).

tff(c_5170,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_80,c_74,c_3378,c_198,c_5151])).

tff(c_5193,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5170])).

tff(c_5204,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_80,c_74,c_5193])).

tff(c_3926,plain,(
    ! [B_352,D_353,A_354,C_355] :
      ( k1_xboole_0 = B_352
      | v1_funct_2(D_353,A_354,C_355)
      | ~ r1_tarski(B_352,C_355)
      | ~ m1_subset_1(D_353,k1_zfmisc_1(k2_zfmisc_1(A_354,B_352)))
      | ~ v1_funct_2(D_353,A_354,B_352)
      | ~ v1_funct_1(D_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5695,plain,(
    ! [B_459,D_460,A_461,A_462] :
      ( k1_relat_1(B_459) = k1_xboole_0
      | v1_funct_2(D_460,A_461,A_462)
      | ~ m1_subset_1(D_460,k1_zfmisc_1(k2_zfmisc_1(A_461,k1_relat_1(B_459))))
      | ~ v1_funct_2(D_460,A_461,k1_relat_1(B_459))
      | ~ v1_funct_1(D_460)
      | ~ v4_relat_1(B_459,A_462)
      | ~ v1_relat_1(B_459) ) ),
    inference(resolution,[status(thm)],[c_12,c_3926])).

tff(c_5703,plain,(
    ! [A_462] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_462)
      | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_462)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5204,c_5695])).

tff(c_5721,plain,(
    ! [A_462] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_462)
      | ~ v4_relat_1('#skF_3',A_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_198,c_4699,c_5703])).

tff(c_5728,plain,(
    ! [A_463] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_463)
      | ~ v4_relat_1('#skF_3',A_463) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3420,c_5721])).

tff(c_3345,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_5731,plain,(
    ~ v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_5728,c_3345])).

tff(c_5735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_5731])).

tff(c_5736,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3402])).

tff(c_5744,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5736,c_5736,c_107])).

tff(c_3401,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3379,c_20])).

tff(c_3419,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3401])).

tff(c_5738,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5736,c_3419])).

tff(c_5794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5744,c_5738])).

tff(c_5795,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3401])).

tff(c_5796,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3401])).

tff(c_5817,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5795,c_5796])).

tff(c_3380,plain,(
    ! [A_303] :
      ( k1_relat_1(A_303) = k1_xboole_0
      | k2_relat_1(A_303) != k1_xboole_0
      | ~ v1_relat_1(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3386,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_3380])).

tff(c_3390,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_3386])).

tff(c_5797,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5795,c_5795,c_3390])).

tff(c_6265,plain,(
    ! [A_516] :
      ( v1_funct_2(A_516,k1_relat_1(A_516),k2_relat_1(A_516))
      | ~ v1_funct_1(A_516)
      | ~ v1_relat_1(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6271,plain,
    ( v1_funct_2('#skF_3','#skF_3',k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5797,c_6265])).

tff(c_6276,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_80,c_5817,c_6271])).

tff(c_6354,plain,(
    ! [A_524] :
      ( m1_subset_1(A_524,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_524),k2_relat_1(A_524))))
      | ~ v1_funct_1(A_524)
      | ~ v1_relat_1(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6378,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5797,c_6354])).

tff(c_6387,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_80,c_5817,c_6378])).

tff(c_5806,plain,(
    ! [A_7] : v4_relat_1('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5795,c_16])).

tff(c_6202,plain,(
    ! [B_507,A_508] :
      ( r1_tarski(k1_relat_1(B_507),A_508)
      | ~ v4_relat_1(B_507,A_508)
      | ~ v1_relat_1(B_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6216,plain,(
    ! [A_508] :
      ( r1_tarski('#skF_3',A_508)
      | ~ v4_relat_1('#skF_3',A_508)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5797,c_6202])).

tff(c_6221,plain,(
    ! [A_508] : r1_tarski('#skF_3',A_508) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_5806,c_6216])).

tff(c_62,plain,(
    ! [D_27,C_26,B_25] :
      ( v1_funct_2(D_27,k1_xboole_0,C_26)
      | ~ r1_tarski(B_25,C_26)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25)))
      | ~ v1_funct_2(D_27,k1_xboole_0,B_25)
      | ~ v1_funct_1(D_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6467,plain,(
    ! [D_529,C_530,B_531] :
      ( v1_funct_2(D_529,'#skF_3',C_530)
      | ~ r1_tarski(B_531,C_530)
      | ~ m1_subset_1(D_529,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_531)))
      | ~ v1_funct_2(D_529,'#skF_3',B_531)
      | ~ v1_funct_1(D_529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5795,c_5795,c_5795,c_62])).

tff(c_6920,plain,(
    ! [D_571,A_572] :
      ( v1_funct_2(D_571,'#skF_3',A_572)
      | ~ m1_subset_1(D_571,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_2(D_571,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_571) ) ),
    inference(resolution,[status(thm)],[c_6221,c_6467])).

tff(c_6922,plain,(
    ! [A_572] :
      ( v1_funct_2('#skF_3','#skF_3',A_572)
      | ~ v1_funct_2('#skF_3','#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6387,c_6920])).

tff(c_6928,plain,(
    ! [A_572] : v1_funct_2('#skF_3','#skF_3',A_572) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6276,c_6922])).

tff(c_6423,plain,(
    ! [A_526,B_527,C_528] :
      ( k2_relset_1(A_526,B_527,C_528) = k2_relat_1(C_528)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(A_526,B_527))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6439,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_6423])).

tff(c_6447,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5817,c_6439])).

tff(c_6072,plain,(
    ! [A_497] :
      ( k1_relat_1(k2_funct_1(A_497)) = k2_relat_1(A_497)
      | ~ v2_funct_1(A_497)
      | ~ v1_funct_1(A_497)
      | ~ v1_relat_1(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3414,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0
    | k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3378,c_22])).

tff(c_5915,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5795,c_5795,c_3414])).

tff(c_5916,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5915])).

tff(c_6084,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6072,c_5916])).

tff(c_6094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_80,c_74,c_5817,c_6084])).

tff(c_6095,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5915])).

tff(c_6100,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6095,c_3345])).

tff(c_6449,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6447,c_6100])).

tff(c_6948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6928,c_6449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.80/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.41  
% 7.05/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.05/2.41  
% 7.05/2.41  %Foreground sorts:
% 7.05/2.41  
% 7.05/2.41  
% 7.05/2.41  %Background operators:
% 7.05/2.41  
% 7.05/2.41  
% 7.05/2.41  %Foreground operators:
% 7.05/2.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.05/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.05/2.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.05/2.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.05/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.05/2.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.05/2.41  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 7.05/2.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.05/2.41  tff('#skF_2', type, '#skF_2': $i).
% 7.05/2.41  tff('#skF_3', type, '#skF_3': $i).
% 7.05/2.41  tff('#skF_1', type, '#skF_1': $i).
% 7.05/2.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.05/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.05/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.05/2.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.05/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.05/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.05/2.41  
% 7.05/2.44  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.05/2.44  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.05/2.44  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.05/2.44  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.05/2.44  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.05/2.44  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.05/2.44  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.05/2.44  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.05/2.44  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.05/2.44  tff(f_131, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 7.05/2.44  tff(f_62, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 7.05/2.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.05/2.44  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 7.05/2.44  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.05/2.44  tff(f_88, axiom, (![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 7.05/2.44  tff(f_48, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 7.05/2.44  tff(f_34, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.05/2.44  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.05/2.44  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.05/2.44  tff(c_3366, plain, (![C_300, A_301, B_302]: (v1_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.05/2.44  tff(c_3379, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_3366])).
% 7.05/2.44  tff(c_3521, plain, (![C_319, A_320, B_321]: (v4_relat_1(C_319, A_320) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.05/2.44  tff(c_3534, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_3521])).
% 7.05/2.44  tff(c_22, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.05/2.44  tff(c_3402, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3379, c_22])).
% 7.05/2.44  tff(c_3420, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3402])).
% 7.05/2.44  tff(c_172, plain, (![A_39]: (v1_funct_1(k2_funct_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.05/2.44  tff(c_70, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.05/2.44  tff(c_154, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 7.05/2.44  tff(c_175, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_172, c_154])).
% 7.05/2.44  tff(c_178, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_175])).
% 7.05/2.44  tff(c_184, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.05/2.44  tff(c_191, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_184])).
% 7.05/2.44  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_191])).
% 7.05/2.44  tff(c_198, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_70])).
% 7.05/2.44  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.05/2.44  tff(c_32, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.44  tff(c_242, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.05/2.44  tff(c_251, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_242])).
% 7.05/2.44  tff(c_344, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.05/2.44  tff(c_353, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_344])).
% 7.05/2.44  tff(c_263, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_251, c_22])).
% 7.05/2.44  tff(c_265, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_263])).
% 7.05/2.44  tff(c_30, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.05/2.44  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.05/2.44  tff(c_518, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.05/2.44  tff(c_531, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_518])).
% 7.05/2.44  tff(c_537, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_531])).
% 7.05/2.44  tff(c_394, plain, (![A_79]: (k1_relat_1(k2_funct_1(A_79))=k2_relat_1(A_79) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.44  tff(c_54, plain, (![A_23]: (v1_funct_2(A_23, k1_relat_1(A_23), k2_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.05/2.44  tff(c_1146, plain, (![A_142]: (v1_funct_2(k2_funct_1(A_142), k2_relat_1(A_142), k2_relat_1(k2_funct_1(A_142))) | ~v1_funct_1(k2_funct_1(A_142)) | ~v1_relat_1(k2_funct_1(A_142)) | ~v2_funct_1(A_142) | ~v1_funct_1(A_142) | ~v1_relat_1(A_142))), inference(superposition, [status(thm), theory('equality')], [c_394, c_54])).
% 7.05/2.44  tff(c_1155, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_537, c_1146])).
% 7.05/2.44  tff(c_1169, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_80, c_74, c_198, c_1155])).
% 7.05/2.44  tff(c_1172, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1169])).
% 7.05/2.44  tff(c_1175, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1172])).
% 7.05/2.44  tff(c_1179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_80, c_1175])).
% 7.05/2.44  tff(c_1180, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1169])).
% 7.05/2.44  tff(c_1204, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1180])).
% 7.05/2.44  tff(c_1208, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_80, c_74, c_1204])).
% 7.05/2.44  tff(c_1181, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1169])).
% 7.05/2.44  tff(c_34, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.44  tff(c_452, plain, (![A_89]: (m1_subset_1(A_89, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_89), k2_relat_1(A_89)))) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.05/2.44  tff(c_1307, plain, (![A_148]: (m1_subset_1(k2_funct_1(A_148), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_148), k2_relat_1(k2_funct_1(A_148))))) | ~v1_funct_1(k2_funct_1(A_148)) | ~v1_relat_1(k2_funct_1(A_148)) | ~v2_funct_1(A_148) | ~v1_funct_1(A_148) | ~v1_relat_1(A_148))), inference(superposition, [status(thm), theory('equality')], [c_34, c_452])).
% 7.05/2.44  tff(c_1331, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_537, c_1307])).
% 7.05/2.44  tff(c_1350, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_80, c_74, c_1181, c_198, c_1331])).
% 7.05/2.44  tff(c_1373, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1350])).
% 7.05/2.44  tff(c_1383, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_80, c_74, c_1373])).
% 7.05/2.44  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.44  tff(c_1059, plain, (![B_126, D_127, A_128, C_129]: (k1_xboole_0=B_126 | m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_128, C_129))) | ~r1_tarski(B_126, C_129) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_126))) | ~v1_funct_2(D_127, A_128, B_126) | ~v1_funct_1(D_127))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.05/2.44  tff(c_2471, plain, (![B_206, D_207, A_208, A_209]: (k1_relat_1(B_206)=k1_xboole_0 | m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_208, A_209))) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_208, k1_relat_1(B_206)))) | ~v1_funct_2(D_207, A_208, k1_relat_1(B_206)) | ~v1_funct_1(D_207) | ~v4_relat_1(B_206, A_209) | ~v1_relat_1(B_206))), inference(resolution, [status(thm)], [c_12, c_1059])).
% 7.05/2.44  tff(c_2481, plain, (![A_209]: (k1_relat_1('#skF_3')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_209))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v4_relat_1('#skF_3', A_209) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1383, c_2471])).
% 7.05/2.44  tff(c_2498, plain, (![A_209]: (k1_relat_1('#skF_3')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_209))) | ~v4_relat_1('#skF_3', A_209))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_198, c_1208, c_2481])).
% 7.05/2.44  tff(c_2503, plain, (![A_210]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_210))) | ~v4_relat_1('#skF_3', A_210))), inference(negUnitSimplification, [status(thm)], [c_265, c_2498])).
% 7.05/2.44  tff(c_197, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_70])).
% 7.05/2.44  tff(c_207, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_197])).
% 7.05/2.44  tff(c_2532, plain, (~v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_2503, c_207])).
% 7.05/2.44  tff(c_2557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_2532])).
% 7.05/2.44  tff(c_2558, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_263])).
% 7.05/2.44  tff(c_24, plain, (![A_10]: (k1_relat_1(A_10)=k1_xboole_0 | k2_relat_1(A_10)!=k1_xboole_0 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.44  tff(c_261, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_251, c_24])).
% 7.05/2.44  tff(c_2581, plain, (k1_relat_1('#skF_3')='#skF_3' | k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_261])).
% 7.05/2.44  tff(c_2582, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_2581])).
% 7.05/2.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.05/2.44  tff(c_90, plain, (![A_31]: (v1_xboole_0(k2_relat_1(A_31)) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.05/2.44  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.05/2.44  tff(c_99, plain, (![A_32]: (k2_relat_1(A_32)=k1_xboole_0 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_90, c_4])).
% 7.05/2.44  tff(c_107, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_99])).
% 7.05/2.44  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.05/2.44  tff(c_227, plain, (![A_50]: (k1_relat_1(A_50)=k1_xboole_0 | k2_relat_1(A_50)!=k1_xboole_0 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.44  tff(c_233, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_227])).
% 7.05/2.44  tff(c_237, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_233])).
% 7.05/2.44  tff(c_2561, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_237])).
% 7.05/2.44  tff(c_26, plain, (![A_10]: (k2_relat_1(A_10)=k1_xboole_0 | k1_relat_1(A_10)!=k1_xboole_0 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.44  tff(c_2590, plain, (![A_212]: (k2_relat_1(A_212)='#skF_3' | k1_relat_1(A_212)!='#skF_3' | ~v1_relat_1(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_26])).
% 7.05/2.44  tff(c_2593, plain, (k2_relat_1('#skF_3')='#skF_3' | k1_relat_1('#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_251, c_2590])).
% 7.05/2.44  tff(c_2599, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2561, c_2593])).
% 7.05/2.44  tff(c_2601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2582, c_2599])).
% 7.05/2.44  tff(c_2603, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2581])).
% 7.05/2.44  tff(c_20, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.05/2.44  tff(c_262, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_251, c_20])).
% 7.05/2.44  tff(c_264, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_262])).
% 7.05/2.44  tff(c_2560, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_264])).
% 7.05/2.44  tff(c_2623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2603, c_2560])).
% 7.05/2.44  tff(c_2624, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_262])).
% 7.05/2.44  tff(c_16, plain, (![A_7]: (v4_relat_1(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.05/2.44  tff(c_2651, plain, (![A_7]: (v4_relat_1('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2624, c_16])).
% 7.05/2.44  tff(c_2642, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2624, c_2624, c_237])).
% 7.05/2.44  tff(c_2680, plain, (![B_218, A_219]: (r1_tarski(k1_relat_1(B_218), A_219) | ~v4_relat_1(B_218, A_219) | ~v1_relat_1(B_218))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.44  tff(c_2683, plain, (![A_219]: (r1_tarski('#skF_3', A_219) | ~v4_relat_1('#skF_3', A_219) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2642, c_2680])).
% 7.05/2.44  tff(c_2685, plain, (![A_219]: (r1_tarski('#skF_3', A_219))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_2651, c_2683])).
% 7.05/2.44  tff(c_2625, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_262])).
% 7.05/2.44  tff(c_2663, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2624, c_2625])).
% 7.05/2.44  tff(c_208, plain, (![A_46]: (v1_relat_1(k2_funct_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.05/2.44  tff(c_216, plain, (![A_46]: (k1_relat_1(k2_funct_1(A_46))!=k1_xboole_0 | k2_funct_1(A_46)=k1_xboole_0 | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_208, c_22])).
% 7.05/2.44  tff(c_2912, plain, (![A_251]: (k1_relat_1(k2_funct_1(A_251))!='#skF_3' | k2_funct_1(A_251)='#skF_3' | ~v1_funct_1(A_251) | ~v1_relat_1(A_251))), inference(demodulation, [status(thm), theory('equality')], [c_2624, c_2624, c_216])).
% 7.05/2.44  tff(c_3332, plain, (![A_295]: (k2_relat_1(A_295)!='#skF_3' | k2_funct_1(A_295)='#skF_3' | ~v1_funct_1(A_295) | ~v1_relat_1(A_295) | ~v2_funct_1(A_295) | ~v1_funct_1(A_295) | ~v1_relat_1(A_295))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2912])).
% 7.05/2.44  tff(c_3335, plain, (k2_relat_1('#skF_3')!='#skF_3' | k2_funct_1('#skF_3')='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3332])).
% 7.05/2.44  tff(c_3338, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_80, c_2663, c_3335])).
% 7.05/2.44  tff(c_2935, plain, (![A_259, B_260, C_261]: (k2_relset_1(A_259, B_260, C_261)=k2_relat_1(C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.05/2.44  tff(c_2942, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2935])).
% 7.05/2.44  tff(c_2945, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2663, c_72, c_2942])).
% 7.05/2.44  tff(c_8, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.05/2.44  tff(c_226, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_207])).
% 7.05/2.44  tff(c_2946, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2945, c_226])).
% 7.05/2.44  tff(c_3340, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3338, c_2946])).
% 7.05/2.44  tff(c_3344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2685, c_3340])).
% 7.05/2.44  tff(c_3346, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_197])).
% 7.05/2.44  tff(c_3378, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3346, c_3366])).
% 7.05/2.44  tff(c_3626, plain, (![A_331, B_332, C_333]: (k2_relset_1(A_331, B_332, C_333)=k2_relat_1(C_333) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.05/2.44  tff(c_3636, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_3626])).
% 7.05/2.44  tff(c_3640, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3636])).
% 7.05/2.44  tff(c_3571, plain, (![A_326]: (k1_relat_1(k2_funct_1(A_326))=k2_relat_1(A_326) | ~v2_funct_1(A_326) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.44  tff(c_4664, plain, (![A_403]: (v1_funct_2(k2_funct_1(A_403), k2_relat_1(A_403), k2_relat_1(k2_funct_1(A_403))) | ~v1_funct_1(k2_funct_1(A_403)) | ~v1_relat_1(k2_funct_1(A_403)) | ~v2_funct_1(A_403) | ~v1_funct_1(A_403) | ~v1_relat_1(A_403))), inference(superposition, [status(thm), theory('equality')], [c_3571, c_54])).
% 7.05/2.44  tff(c_4673, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3640, c_4664])).
% 7.05/2.44  tff(c_4687, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_80, c_74, c_3378, c_198, c_4673])).
% 7.05/2.44  tff(c_4695, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_4687])).
% 7.05/2.44  tff(c_4699, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_80, c_74, c_4695])).
% 7.05/2.44  tff(c_3658, plain, (![A_334]: (m1_subset_1(A_334, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_334), k2_relat_1(A_334)))) | ~v1_funct_1(A_334) | ~v1_relat_1(A_334))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.05/2.44  tff(c_5127, plain, (![A_424]: (m1_subset_1(k2_funct_1(A_424), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_424), k2_relat_1(k2_funct_1(A_424))))) | ~v1_funct_1(k2_funct_1(A_424)) | ~v1_relat_1(k2_funct_1(A_424)) | ~v2_funct_1(A_424) | ~v1_funct_1(A_424) | ~v1_relat_1(A_424))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3658])).
% 7.05/2.44  tff(c_5151, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3640, c_5127])).
% 7.05/2.44  tff(c_5170, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_80, c_74, c_3378, c_198, c_5151])).
% 7.05/2.44  tff(c_5193, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_5170])).
% 7.05/2.44  tff(c_5204, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_80, c_74, c_5193])).
% 7.05/2.44  tff(c_3926, plain, (![B_352, D_353, A_354, C_355]: (k1_xboole_0=B_352 | v1_funct_2(D_353, A_354, C_355) | ~r1_tarski(B_352, C_355) | ~m1_subset_1(D_353, k1_zfmisc_1(k2_zfmisc_1(A_354, B_352))) | ~v1_funct_2(D_353, A_354, B_352) | ~v1_funct_1(D_353))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.05/2.44  tff(c_5695, plain, (![B_459, D_460, A_461, A_462]: (k1_relat_1(B_459)=k1_xboole_0 | v1_funct_2(D_460, A_461, A_462) | ~m1_subset_1(D_460, k1_zfmisc_1(k2_zfmisc_1(A_461, k1_relat_1(B_459)))) | ~v1_funct_2(D_460, A_461, k1_relat_1(B_459)) | ~v1_funct_1(D_460) | ~v4_relat_1(B_459, A_462) | ~v1_relat_1(B_459))), inference(resolution, [status(thm)], [c_12, c_3926])).
% 7.05/2.44  tff(c_5703, plain, (![A_462]: (k1_relat_1('#skF_3')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_462) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v4_relat_1('#skF_3', A_462) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5204, c_5695])).
% 7.05/2.44  tff(c_5721, plain, (![A_462]: (k1_relat_1('#skF_3')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_462) | ~v4_relat_1('#skF_3', A_462))), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_198, c_4699, c_5703])).
% 7.05/2.44  tff(c_5728, plain, (![A_463]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_463) | ~v4_relat_1('#skF_3', A_463))), inference(negUnitSimplification, [status(thm)], [c_3420, c_5721])).
% 7.05/2.44  tff(c_3345, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_197])).
% 7.05/2.44  tff(c_5731, plain, (~v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_5728, c_3345])).
% 7.05/2.44  tff(c_5735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3534, c_5731])).
% 7.05/2.44  tff(c_5736, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3402])).
% 7.05/2.44  tff(c_5744, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5736, c_5736, c_107])).
% 7.05/2.44  tff(c_3401, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3379, c_20])).
% 7.05/2.44  tff(c_3419, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3401])).
% 7.05/2.44  tff(c_5738, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5736, c_3419])).
% 7.05/2.44  tff(c_5794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5744, c_5738])).
% 7.05/2.44  tff(c_5795, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3401])).
% 7.05/2.44  tff(c_5796, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3401])).
% 7.05/2.44  tff(c_5817, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5795, c_5796])).
% 7.05/2.44  tff(c_3380, plain, (![A_303]: (k1_relat_1(A_303)=k1_xboole_0 | k2_relat_1(A_303)!=k1_xboole_0 | ~v1_relat_1(A_303))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.44  tff(c_3386, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_3380])).
% 7.05/2.44  tff(c_3390, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_3386])).
% 7.05/2.44  tff(c_5797, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5795, c_5795, c_3390])).
% 7.05/2.44  tff(c_6265, plain, (![A_516]: (v1_funct_2(A_516, k1_relat_1(A_516), k2_relat_1(A_516)) | ~v1_funct_1(A_516) | ~v1_relat_1(A_516))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.05/2.44  tff(c_6271, plain, (v1_funct_2('#skF_3', '#skF_3', k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5797, c_6265])).
% 7.05/2.44  tff(c_6276, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_80, c_5817, c_6271])).
% 7.05/2.44  tff(c_6354, plain, (![A_524]: (m1_subset_1(A_524, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_524), k2_relat_1(A_524)))) | ~v1_funct_1(A_524) | ~v1_relat_1(A_524))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.05/2.44  tff(c_6378, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5797, c_6354])).
% 7.05/2.44  tff(c_6387, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_80, c_5817, c_6378])).
% 7.05/2.44  tff(c_5806, plain, (![A_7]: (v4_relat_1('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_5795, c_16])).
% 7.05/2.44  tff(c_6202, plain, (![B_507, A_508]: (r1_tarski(k1_relat_1(B_507), A_508) | ~v4_relat_1(B_507, A_508) | ~v1_relat_1(B_507))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.05/2.44  tff(c_6216, plain, (![A_508]: (r1_tarski('#skF_3', A_508) | ~v4_relat_1('#skF_3', A_508) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5797, c_6202])).
% 7.05/2.44  tff(c_6221, plain, (![A_508]: (r1_tarski('#skF_3', A_508))), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_5806, c_6216])).
% 7.05/2.44  tff(c_62, plain, (![D_27, C_26, B_25]: (v1_funct_2(D_27, k1_xboole_0, C_26) | ~r1_tarski(B_25, C_26) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))) | ~v1_funct_2(D_27, k1_xboole_0, B_25) | ~v1_funct_1(D_27))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.05/2.44  tff(c_6467, plain, (![D_529, C_530, B_531]: (v1_funct_2(D_529, '#skF_3', C_530) | ~r1_tarski(B_531, C_530) | ~m1_subset_1(D_529, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_531))) | ~v1_funct_2(D_529, '#skF_3', B_531) | ~v1_funct_1(D_529))), inference(demodulation, [status(thm), theory('equality')], [c_5795, c_5795, c_5795, c_62])).
% 7.05/2.44  tff(c_6920, plain, (![D_571, A_572]: (v1_funct_2(D_571, '#skF_3', A_572) | ~m1_subset_1(D_571, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2(D_571, '#skF_3', '#skF_3') | ~v1_funct_1(D_571))), inference(resolution, [status(thm)], [c_6221, c_6467])).
% 7.05/2.44  tff(c_6922, plain, (![A_572]: (v1_funct_2('#skF_3', '#skF_3', A_572) | ~v1_funct_2('#skF_3', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_6387, c_6920])).
% 7.05/2.44  tff(c_6928, plain, (![A_572]: (v1_funct_2('#skF_3', '#skF_3', A_572))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6276, c_6922])).
% 7.05/2.44  tff(c_6423, plain, (![A_526, B_527, C_528]: (k2_relset_1(A_526, B_527, C_528)=k2_relat_1(C_528) | ~m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(A_526, B_527))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.05/2.44  tff(c_6439, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_6423])).
% 7.05/2.44  tff(c_6447, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5817, c_6439])).
% 7.05/2.44  tff(c_6072, plain, (![A_497]: (k1_relat_1(k2_funct_1(A_497))=k2_relat_1(A_497) | ~v2_funct_1(A_497) | ~v1_funct_1(A_497) | ~v1_relat_1(A_497))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.05/2.44  tff(c_3414, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0 | k2_funct_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3378, c_22])).
% 7.05/2.44  tff(c_5915, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5795, c_5795, c_3414])).
% 7.05/2.44  tff(c_5916, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_5915])).
% 7.05/2.44  tff(c_6084, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6072, c_5916])).
% 7.05/2.44  tff(c_6094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3379, c_80, c_74, c_5817, c_6084])).
% 7.05/2.44  tff(c_6095, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_5915])).
% 7.05/2.44  tff(c_6100, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6095, c_3345])).
% 7.05/2.44  tff(c_6449, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6447, c_6100])).
% 7.05/2.44  tff(c_6948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6928, c_6449])).
% 7.05/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.44  
% 7.05/2.44  Inference rules
% 7.05/2.44  ----------------------
% 7.05/2.44  #Ref     : 0
% 7.05/2.44  #Sup     : 1532
% 7.05/2.44  #Fact    : 0
% 7.05/2.44  #Define  : 0
% 7.05/2.44  #Split   : 22
% 7.05/2.44  #Chain   : 0
% 7.05/2.44  #Close   : 0
% 7.05/2.44  
% 7.05/2.44  Ordering : KBO
% 7.05/2.44  
% 7.05/2.44  Simplification rules
% 7.05/2.44  ----------------------
% 7.05/2.44  #Subsume      : 260
% 7.05/2.44  #Demod        : 1731
% 7.05/2.44  #Tautology    : 602
% 7.05/2.44  #SimpNegUnit  : 30
% 7.05/2.44  #BackRed      : 143
% 7.05/2.44  
% 7.05/2.44  #Partial instantiations: 0
% 7.05/2.44  #Strategies tried      : 1
% 7.05/2.44  
% 7.05/2.44  Timing (in seconds)
% 7.05/2.44  ----------------------
% 7.05/2.44  Preprocessing        : 0.33
% 7.05/2.44  Parsing              : 0.18
% 7.05/2.44  CNF conversion       : 0.02
% 7.05/2.44  Main loop            : 1.32
% 7.05/2.44  Inferencing          : 0.44
% 7.05/2.44  Reduction            : 0.44
% 7.05/2.44  Demodulation         : 0.31
% 7.05/2.44  BG Simplification    : 0.05
% 7.05/2.44  Subsumption          : 0.29
% 7.05/2.44  Abstraction          : 0.05
% 7.05/2.44  MUC search           : 0.00
% 7.05/2.44  Cooper               : 0.00
% 7.05/2.44  Total                : 1.72
% 7.05/2.44  Index Insertion      : 0.00
% 7.05/2.44  Index Deletion       : 0.00
% 7.05/2.44  Index Matching       : 0.00
% 7.05/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
