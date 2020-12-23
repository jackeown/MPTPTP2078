%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:00 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 384 expanded)
%              Number of leaves         :   28 ( 148 expanded)
%              Depth                    :   12
%              Number of atoms          :  209 (1247 expanded)
%              Number of equality atoms :   59 ( 348 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
            <=> ! [D] :
                  ( r2_hidden(D,k1_relset_1(A,A,B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_40,plain,
    ( k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_65,plain,(
    ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_66,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_91,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_91])).

tff(c_133,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k1_relset_1(A_52,B_53,C_54),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_133])).

tff(c_157,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_150])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_176,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_104,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_312,plain,(
    ! [B_87,A_88,C_89] :
      ( k1_xboole_0 = B_87
      | k1_relset_1(A_88,B_87,C_89) = A_88
      | ~ v1_funct_2(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_326,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_312])).

tff(c_334,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_104,c_326])).

tff(c_343,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_335,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90,B_91),k1_relat_1(A_90))
      | r1_partfun1(A_90,B_91)
      | ~ r1_tarski(k1_relat_1(A_90),k1_relat_1(B_91))
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_50,plain,(
    ! [D_32] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_32) = k1_funct_1('#skF_4',D_32)
      | ~ r2_hidden(D_32,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_113,plain,(
    ! [D_32] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_32) = k1_funct_1('#skF_4',D_32)
      | ~ r2_hidden(D_32,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_50])).

tff(c_114,plain,(
    ! [D_32] :
      ( k1_funct_1('#skF_3',D_32) = k1_funct_1('#skF_4',D_32)
      | ~ r2_hidden(D_32,k1_relat_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_113])).

tff(c_339,plain,(
    ! [B_91] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_91)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_91))
      | r1_partfun1('#skF_3',B_91)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_91))
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_335,c_114])).

tff(c_449,plain,(
    ! [B_105] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_105)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_105))
      | r1_partfun1('#skF_3',B_105)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_105))
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_38,c_339])).

tff(c_452,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_449])).

tff(c_454,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_34,c_176,c_452])).

tff(c_455,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_454])).

tff(c_483,plain,(
    ! [B_124,A_125] :
      ( k1_funct_1(B_124,'#skF_1'(A_125,B_124)) != k1_funct_1(A_125,'#skF_1'(A_125,B_124))
      | r1_partfun1(A_125,B_124)
      | ~ r1_tarski(k1_relat_1(A_125),k1_relat_1(B_124))
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_485,plain,
    ( r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_483])).

tff(c_488,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_38,c_79,c_34,c_176,c_343,c_485])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_488])).

tff(c_492,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_52,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_491,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_228,plain,(
    ! [B_69,C_70] :
      ( k1_relset_1(k1_xboole_0,B_69,C_70) = k1_xboole_0
      | ~ v1_funct_2(C_70,k1_xboole_0,B_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_238,plain,(
    ! [B_69,A_1] :
      ( k1_relset_1(k1_xboole_0,B_69,A_1) = k1_xboole_0
      | ~ v1_funct_2(A_1,k1_xboole_0,B_69)
      | ~ r1_tarski(A_1,k2_zfmisc_1(k1_xboole_0,B_69)) ) ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_577,plain,(
    ! [B_138,A_139] :
      ( k1_relset_1('#skF_2',B_138,A_139) = '#skF_2'
      | ~ v1_funct_2(A_139,'#skF_2',B_138)
      | ~ r1_tarski(A_139,k2_zfmisc_1('#skF_2',B_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_491,c_491,c_491,c_238])).

tff(c_584,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_577])).

tff(c_591,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_104,c_584])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_591])).

tff(c_594,plain,(
    k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_598,plain,(
    ! [C_140,A_141,B_142] :
      ( v1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_611,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_598])).

tff(c_623,plain,(
    ! [A_146,B_147,C_148] :
      ( k1_relset_1(A_146,B_147,C_148) = k1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_635,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_623])).

tff(c_664,plain,(
    ! [A_154,B_155,C_156] :
      ( m1_subset_1(k1_relset_1(A_154,B_155,C_156),k1_zfmisc_1(A_154))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_681,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_664])).

tff(c_688,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_681])).

tff(c_707,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_688,c_2])).

tff(c_595,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_636,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_623])).

tff(c_843,plain,(
    ! [B_189,A_190,C_191] :
      ( k1_xboole_0 = B_189
      | k1_relset_1(A_190,B_189,C_191) = A_190
      | ~ v1_funct_2(C_191,A_190,B_189)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_857,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_843])).

tff(c_865,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_636,c_857])).

tff(c_866,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_865])).

tff(c_610,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_598])).

tff(c_42,plain,
    ( r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3'))
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_597,plain,(
    r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_42])).

tff(c_642,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_597])).

tff(c_960,plain,(
    ! [B_202,C_203,A_204] :
      ( k1_funct_1(B_202,C_203) = k1_funct_1(A_204,C_203)
      | ~ r2_hidden(C_203,k1_relat_1(A_204))
      | ~ r1_partfun1(A_204,B_202)
      | ~ r1_tarski(k1_relat_1(A_204),k1_relat_1(B_202))
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202)
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_966,plain,(
    ! [B_202] :
      ( k1_funct_1(B_202,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_202)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_202))
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_642,c_960])).

tff(c_973,plain,(
    ! [B_205] :
      ( k1_funct_1(B_205,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_205)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_205))
      | ~ v1_funct_1(B_205)
      | ~ v1_relat_1(B_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_38,c_966])).

tff(c_976,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_973])).

tff(c_978,plain,(
    k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_34,c_707,c_595,c_976])).

tff(c_980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_978])).

tff(c_982,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_981,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_776,plain,(
    ! [B_175,C_176] :
      ( k1_relset_1(k1_xboole_0,B_175,C_176) = k1_xboole_0
      | ~ v1_funct_2(C_176,k1_xboole_0,B_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_786,plain,(
    ! [B_175,A_1] :
      ( k1_relset_1(k1_xboole_0,B_175,A_1) = k1_xboole_0
      | ~ v1_funct_2(A_1,k1_xboole_0,B_175)
      | ~ r1_tarski(A_1,k2_zfmisc_1(k1_xboole_0,B_175)) ) ),
    inference(resolution,[status(thm)],[c_4,c_776])).

tff(c_1039,plain,(
    ! [B_212,A_213] :
      ( k1_relset_1('#skF_2',B_212,A_213) = '#skF_2'
      | ~ v1_funct_2(A_213,'#skF_2',B_212)
      | ~ r1_tarski(A_213,k2_zfmisc_1('#skF_2',B_212)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_981,c_981,c_981,c_786])).

tff(c_1046,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1039])).

tff(c_1053,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_636,c_1046])).

tff(c_1055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_982,c_1053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/2.15  
% 4.35/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/2.16  %$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.35/2.16  
% 4.35/2.16  %Foreground sorts:
% 4.35/2.16  
% 4.35/2.16  
% 4.35/2.16  %Background operators:
% 4.35/2.16  
% 4.35/2.16  
% 4.35/2.16  %Foreground operators:
% 4.35/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.35/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/2.16  tff('#skF_5', type, '#skF_5': $i).
% 4.35/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.35/2.16  tff('#skF_2', type, '#skF_2': $i).
% 4.35/2.16  tff('#skF_3', type, '#skF_3': $i).
% 4.35/2.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.35/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/2.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.35/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.35/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.35/2.16  tff('#skF_4', type, '#skF_4': $i).
% 4.35/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.35/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.35/2.16  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 4.35/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/2.16  
% 4.35/2.19  tff(f_96, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) <=> (![D]: (r2_hidden(D, k1_relset_1(A, A, B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_2)).
% 4.35/2.19  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.35/2.19  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.35/2.19  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.35/2.19  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.35/2.19  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.35/2.19  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 4.35/2.19  tff(c_40, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.35/2.19  tff(c_65, plain, (~r1_partfun1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 4.35/2.19  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.35/2.19  tff(c_66, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.35/2.19  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_66])).
% 4.35/2.19  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.35/2.19  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.35/2.19  tff(c_79, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_66])).
% 4.35/2.19  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.35/2.19  tff(c_91, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.35/2.19  tff(c_103, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_91])).
% 4.35/2.19  tff(c_133, plain, (![A_52, B_53, C_54]: (m1_subset_1(k1_relset_1(A_52, B_53, C_54), k1_zfmisc_1(A_52)) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.35/2.19  tff(c_150, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_103, c_133])).
% 4.35/2.19  tff(c_157, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_150])).
% 4.35/2.19  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.35/2.19  tff(c_176, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_157, c_2])).
% 4.35/2.19  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.35/2.19  tff(c_104, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_91])).
% 4.35/2.19  tff(c_312, plain, (![B_87, A_88, C_89]: (k1_xboole_0=B_87 | k1_relset_1(A_88, B_87, C_89)=A_88 | ~v1_funct_2(C_89, A_88, B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.35/2.19  tff(c_326, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_312])).
% 4.35/2.19  tff(c_334, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_104, c_326])).
% 4.35/2.19  tff(c_343, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_334])).
% 4.35/2.19  tff(c_335, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90, B_91), k1_relat_1(A_90)) | r1_partfun1(A_90, B_91) | ~r1_tarski(k1_relat_1(A_90), k1_relat_1(B_91)) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.35/2.19  tff(c_50, plain, (![D_32]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_32)=k1_funct_1('#skF_4', D_32) | ~r2_hidden(D_32, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.35/2.19  tff(c_113, plain, (![D_32]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_32)=k1_funct_1('#skF_4', D_32) | ~r2_hidden(D_32, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_50])).
% 4.35/2.19  tff(c_114, plain, (![D_32]: (k1_funct_1('#skF_3', D_32)=k1_funct_1('#skF_4', D_32) | ~r2_hidden(D_32, k1_relat_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_65, c_113])).
% 4.35/2.19  tff(c_339, plain, (![B_91]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_91))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_91)) | r1_partfun1('#skF_3', B_91) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_91)) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_335, c_114])).
% 4.35/2.19  tff(c_449, plain, (![B_105]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_105))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_105)) | r1_partfun1('#skF_3', B_105) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_105)) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_38, c_339])).
% 4.35/2.19  tff(c_452, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_343, c_449])).
% 4.35/2.19  tff(c_454, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_34, c_176, c_452])).
% 4.35/2.19  tff(c_455, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_65, c_454])).
% 4.35/2.19  tff(c_483, plain, (![B_124, A_125]: (k1_funct_1(B_124, '#skF_1'(A_125, B_124))!=k1_funct_1(A_125, '#skF_1'(A_125, B_124)) | r1_partfun1(A_125, B_124) | ~r1_tarski(k1_relat_1(A_125), k1_relat_1(B_124)) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.35/2.19  tff(c_485, plain, (r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_455, c_483])).
% 4.35/2.19  tff(c_488, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_38, c_79, c_34, c_176, c_343, c_485])).
% 4.35/2.19  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_488])).
% 4.35/2.19  tff(c_492, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_334])).
% 4.35/2.19  tff(c_52, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.35/2.19  tff(c_64, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_52])).
% 4.35/2.19  tff(c_491, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_334])).
% 4.35/2.19  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.35/2.19  tff(c_228, plain, (![B_69, C_70]: (k1_relset_1(k1_xboole_0, B_69, C_70)=k1_xboole_0 | ~v1_funct_2(C_70, k1_xboole_0, B_69) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_69))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.35/2.19  tff(c_238, plain, (![B_69, A_1]: (k1_relset_1(k1_xboole_0, B_69, A_1)=k1_xboole_0 | ~v1_funct_2(A_1, k1_xboole_0, B_69) | ~r1_tarski(A_1, k2_zfmisc_1(k1_xboole_0, B_69)))), inference(resolution, [status(thm)], [c_4, c_228])).
% 4.35/2.19  tff(c_577, plain, (![B_138, A_139]: (k1_relset_1('#skF_2', B_138, A_139)='#skF_2' | ~v1_funct_2(A_139, '#skF_2', B_138) | ~r1_tarski(A_139, k2_zfmisc_1('#skF_2', B_138)))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_491, c_491, c_491, c_238])).
% 4.35/2.19  tff(c_584, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_577])).
% 4.35/2.19  tff(c_591, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_104, c_584])).
% 4.35/2.19  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_591])).
% 4.35/2.19  tff(c_594, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 4.35/2.19  tff(c_598, plain, (![C_140, A_141, B_142]: (v1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.35/2.19  tff(c_611, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_598])).
% 4.35/2.19  tff(c_623, plain, (![A_146, B_147, C_148]: (k1_relset_1(A_146, B_147, C_148)=k1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.35/2.19  tff(c_635, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_623])).
% 4.35/2.19  tff(c_664, plain, (![A_154, B_155, C_156]: (m1_subset_1(k1_relset_1(A_154, B_155, C_156), k1_zfmisc_1(A_154)) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.35/2.19  tff(c_681, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_635, c_664])).
% 4.35/2.19  tff(c_688, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_681])).
% 4.35/2.19  tff(c_707, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_688, c_2])).
% 4.35/2.19  tff(c_595, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 4.35/2.19  tff(c_636, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_623])).
% 4.35/2.19  tff(c_843, plain, (![B_189, A_190, C_191]: (k1_xboole_0=B_189 | k1_relset_1(A_190, B_189, C_191)=A_190 | ~v1_funct_2(C_191, A_190, B_189) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.35/2.19  tff(c_857, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_843])).
% 4.35/2.19  tff(c_865, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_636, c_857])).
% 4.35/2.19  tff(c_866, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_865])).
% 4.35/2.19  tff(c_610, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_598])).
% 4.35/2.19  tff(c_42, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3')) | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.35/2.19  tff(c_597, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_595, c_42])).
% 4.35/2.19  tff(c_642, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_597])).
% 4.35/2.19  tff(c_960, plain, (![B_202, C_203, A_204]: (k1_funct_1(B_202, C_203)=k1_funct_1(A_204, C_203) | ~r2_hidden(C_203, k1_relat_1(A_204)) | ~r1_partfun1(A_204, B_202) | ~r1_tarski(k1_relat_1(A_204), k1_relat_1(B_202)) | ~v1_funct_1(B_202) | ~v1_relat_1(B_202) | ~v1_funct_1(A_204) | ~v1_relat_1(A_204))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.35/2.19  tff(c_966, plain, (![B_202]: (k1_funct_1(B_202, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_202) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_202)) | ~v1_funct_1(B_202) | ~v1_relat_1(B_202) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_642, c_960])).
% 4.35/2.19  tff(c_973, plain, (![B_205]: (k1_funct_1(B_205, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_205) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_205)) | ~v1_funct_1(B_205) | ~v1_relat_1(B_205))), inference(demodulation, [status(thm), theory('equality')], [c_610, c_38, c_966])).
% 4.35/2.19  tff(c_976, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_866, c_973])).
% 4.35/2.19  tff(c_978, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_34, c_707, c_595, c_976])).
% 4.35/2.19  tff(c_980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_594, c_978])).
% 4.35/2.19  tff(c_982, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_865])).
% 4.35/2.19  tff(c_981, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_865])).
% 4.35/2.19  tff(c_776, plain, (![B_175, C_176]: (k1_relset_1(k1_xboole_0, B_175, C_176)=k1_xboole_0 | ~v1_funct_2(C_176, k1_xboole_0, B_175) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_175))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.35/2.19  tff(c_786, plain, (![B_175, A_1]: (k1_relset_1(k1_xboole_0, B_175, A_1)=k1_xboole_0 | ~v1_funct_2(A_1, k1_xboole_0, B_175) | ~r1_tarski(A_1, k2_zfmisc_1(k1_xboole_0, B_175)))), inference(resolution, [status(thm)], [c_4, c_776])).
% 4.35/2.19  tff(c_1039, plain, (![B_212, A_213]: (k1_relset_1('#skF_2', B_212, A_213)='#skF_2' | ~v1_funct_2(A_213, '#skF_2', B_212) | ~r1_tarski(A_213, k2_zfmisc_1('#skF_2', B_212)))), inference(demodulation, [status(thm), theory('equality')], [c_981, c_981, c_981, c_981, c_786])).
% 4.35/2.19  tff(c_1046, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_1039])).
% 4.35/2.19  tff(c_1053, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_636, c_1046])).
% 4.35/2.19  tff(c_1055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_982, c_1053])).
% 4.35/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/2.19  
% 4.35/2.19  Inference rules
% 4.35/2.19  ----------------------
% 4.35/2.19  #Ref     : 1
% 4.35/2.19  #Sup     : 192
% 4.35/2.19  #Fact    : 0
% 4.35/2.19  #Define  : 0
% 4.35/2.19  #Split   : 7
% 4.35/2.19  #Chain   : 0
% 4.35/2.19  #Close   : 0
% 4.35/2.19  
% 4.35/2.19  Ordering : KBO
% 4.35/2.19  
% 4.35/2.19  Simplification rules
% 4.35/2.19  ----------------------
% 4.35/2.19  #Subsume      : 18
% 4.35/2.19  #Demod        : 198
% 4.35/2.19  #Tautology    : 62
% 4.35/2.19  #SimpNegUnit  : 10
% 4.35/2.19  #BackRed      : 29
% 4.35/2.19  
% 4.35/2.19  #Partial instantiations: 0
% 4.35/2.19  #Strategies tried      : 1
% 4.35/2.19  
% 4.35/2.19  Timing (in seconds)
% 4.35/2.19  ----------------------
% 4.35/2.19  Preprocessing        : 0.52
% 4.35/2.19  Parsing              : 0.25
% 4.35/2.19  CNF conversion       : 0.04
% 4.35/2.19  Main loop            : 0.73
% 4.35/2.19  Inferencing          : 0.29
% 4.35/2.19  Reduction            : 0.21
% 4.35/2.19  Demodulation         : 0.15
% 4.35/2.19  BG Simplification    : 0.04
% 4.35/2.19  Subsumption          : 0.12
% 4.35/2.19  Abstraction          : 0.04
% 4.35/2.19  MUC search           : 0.00
% 4.35/2.19  Cooper               : 0.00
% 4.35/2.19  Total                : 1.32
% 4.35/2.19  Index Insertion      : 0.00
% 4.35/2.19  Index Deletion       : 0.00
% 4.35/2.19  Index Matching       : 0.00
% 4.35/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
