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
% DateTime   : Thu Dec  3 10:12:26 EST 2020

% Result     : Theorem 6.56s
% Output     : CNFRefutation 6.56s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 757 expanded)
%              Number of leaves         :   43 ( 265 expanded)
%              Depth                    :   13
%              Number of atoms          :  313 (2022 expanded)
%              Number of equality atoms :  107 ( 467 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
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

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_153,axiom,(
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
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_90,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_5101,plain,(
    ! [C_199,A_200,B_201] :
      ( v1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5113,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_5101])).

tff(c_94,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_86,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_5320,plain,(
    ! [A_217,B_218,C_219] :
      ( k2_relset_1(A_217,B_218,C_219) = k2_relat_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5326,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_5320])).

tff(c_5333,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_5326])).

tff(c_50,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_337,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_345,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_337])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_524,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_527,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_524])).

tff(c_533,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_527])).

tff(c_30,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) = k1_xboole_0
      | k2_relat_1(A_12) != k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_354,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_345,c_30])).

tff(c_364,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_547,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_364])).

tff(c_92,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_536,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_544,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_536])).

tff(c_1161,plain,(
    ! [B_111,A_112,C_113] :
      ( k1_xboole_0 = B_111
      | k1_relset_1(A_112,B_111,C_113) = A_112
      | ~ v1_funct_2(C_113,A_112,B_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1167,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_1161])).

tff(c_1175,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_544,c_1167])).

tff(c_1176,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_1175])).

tff(c_48,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_396,plain,(
    ! [A_71] :
      ( k1_relat_1(k2_funct_1(A_71)) = k2_relat_1(A_71)
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_24,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(k1_relat_1(A_11))
      | ~ v1_relat_1(A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1977,plain,(
    ! [A_140] :
      ( ~ v1_xboole_0(k2_relat_1(A_140))
      | ~ v1_relat_1(k2_funct_1(A_140))
      | v1_xboole_0(k2_funct_1(A_140))
      | ~ v2_funct_1(A_140)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_24])).

tff(c_1983,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_1977])).

tff(c_1996,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_94,c_88,c_1983])).

tff(c_2001,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1996])).

tff(c_2004,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_2001])).

tff(c_2008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_94,c_2004])).

tff(c_2010,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1996])).

tff(c_44,plain,(
    ! [A_16] :
      ( v1_funct_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_84,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_228,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_231,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_228])).

tff(c_234,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_231])).

tff(c_278,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_281,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_278])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_281])).

tff(c_291,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_869,plain,(
    ! [B_103,A_104] :
      ( m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_103),A_104)))
      | ~ r1_tarski(k2_relat_1(B_103),A_104)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4726,plain,(
    ! [A_182,A_183] :
      ( m1_subset_1(k2_funct_1(A_182),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_182),A_183)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_182)),A_183)
      | ~ v1_funct_1(k2_funct_1(A_182))
      | ~ v1_relat_1(k2_funct_1(A_182))
      | ~ v2_funct_1(A_182)
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_869])).

tff(c_4777,plain,(
    ! [A_183] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_183)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_183)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_4726])).

tff(c_4809,plain,(
    ! [A_184] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_184)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_94,c_88,c_2010,c_291,c_4777])).

tff(c_290,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_320,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_4844,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4809,c_320])).

tff(c_4850,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4844])).

tff(c_4855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_94,c_88,c_10,c_1176,c_4850])).

tff(c_4856,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_4861,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4856,c_24])).

tff(c_4865,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_2,c_4861])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4881,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4865,c_4])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4896,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4881,c_14])).

tff(c_129,plain,(
    ! [A_41] :
      ( v1_xboole_0(k4_relat_1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [A_41] :
      ( k4_relat_1(A_41) = k1_xboole_0
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_129,c_4])).

tff(c_4880,plain,(
    k4_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4865,c_139])).

tff(c_4937,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4881,c_4880])).

tff(c_4926,plain,(
    ! [A_186] :
      ( k4_relat_1(A_186) = k2_funct_1(A_186)
      | ~ v2_funct_1(A_186)
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4932,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_4926])).

tff(c_4936,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_94,c_4932])).

tff(c_4959,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4937,c_4936])).

tff(c_4960,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4959,c_320])).

tff(c_5083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4896,c_4960])).

tff(c_5084,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_5085,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_5336,plain,(
    ! [A_220,B_221,C_222] :
      ( k1_relset_1(A_220,B_221,C_222) = k1_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5347,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5085,c_5336])).

tff(c_5925,plain,(
    ! [B_250,C_251,A_252] :
      ( k1_xboole_0 = B_250
      | v1_funct_2(C_251,A_252,B_250)
      | k1_relset_1(A_252,B_250,C_251) != A_252
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_252,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_5931,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_5085,c_5925])).

tff(c_5941,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5347,c_5931])).

tff(c_5942,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5084,c_5941])).

tff(c_5948,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5942])).

tff(c_5951,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_5948])).

tff(c_5954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5113,c_94,c_88,c_5333,c_5951])).

tff(c_5955,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5942])).

tff(c_5122,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5113,c_30])).

tff(c_5132,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5122])).

tff(c_5351,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5333,c_5132])).

tff(c_5970,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5955,c_5351])).

tff(c_32,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) = k1_xboole_0
      | k1_relat_1(A_12) != k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5123,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5113,c_32])).

tff(c_5133,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5132,c_5123])).

tff(c_5978,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5955,c_5133])).

tff(c_5348,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_5336])).

tff(c_76,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_6014,plain,(
    ! [B_253,A_254,C_255] :
      ( B_253 = '#skF_1'
      | k1_relset_1(A_254,B_253,C_255) = A_254
      | ~ v1_funct_2(C_255,A_254,B_253)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_254,B_253))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5955,c_76])).

tff(c_6023,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_6014])).

tff(c_6029,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_5348,c_6023])).

tff(c_6030,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_5978,c_6029])).

tff(c_6032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5970,c_6030])).

tff(c_6033,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5122])).

tff(c_6102,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6033,c_24])).

tff(c_6106,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5113,c_2,c_6102])).

tff(c_6121,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6106,c_4])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6137,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6121,c_12])).

tff(c_6034,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5122])).

tff(c_6151,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6121,c_6034])).

tff(c_6039,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6033,c_24])).

tff(c_6043,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5113,c_2,c_6039])).

tff(c_6058,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6043,c_4])).

tff(c_6035,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5123])).

tff(c_6094,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6058,c_6035])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6076,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6058,c_6058,c_28])).

tff(c_6096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6094,c_6076])).

tff(c_6098,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5123])).

tff(c_6158,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6121,c_6098])).

tff(c_6488,plain,(
    ! [B_292,A_293] :
      ( v1_funct_2(B_292,k1_relat_1(B_292),A_293)
      | ~ r1_tarski(k2_relat_1(B_292),A_293)
      | ~ v1_funct_1(B_292)
      | ~ v1_relat_1(B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6497,plain,(
    ! [A_293] :
      ( v1_funct_2('#skF_3','#skF_3',A_293)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_293)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6158,c_6488])).

tff(c_6499,plain,(
    ! [A_293] : v1_funct_2('#skF_3','#skF_3',A_293) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5113,c_94,c_6137,c_6151,c_6497])).

tff(c_6135,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6121,c_14])).

tff(c_6453,plain,(
    ! [A_282,B_283,C_284] :
      ( k2_relset_1(A_282,B_283,C_284) = k2_relat_1(C_284)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6457,plain,(
    ! [A_282,B_283] : k2_relset_1(A_282,B_283,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6135,c_6453])).

tff(c_6459,plain,(
    ! [A_282,B_283] : k2_relset_1(A_282,B_283,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6151,c_6457])).

tff(c_6460,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6459,c_86])).

tff(c_6120,plain,(
    k4_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6106,c_139])).

tff(c_6174,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6121,c_6120])).

tff(c_6281,plain,(
    ! [A_271] :
      ( k4_relat_1(A_271) = k2_funct_1(A_271)
      | ~ v2_funct_1(A_271)
      | ~ v1_funct_1(A_271)
      | ~ v1_relat_1(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6287,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_6281])).

tff(c_6291,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5113,c_94,c_6174,c_6287])).

tff(c_6295,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6291,c_5084])).

tff(c_6468,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6460,c_6295])).

tff(c_6502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6499,c_6468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.56/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.34  
% 6.56/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.34  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.56/2.34  
% 6.56/2.34  %Foreground sorts:
% 6.56/2.34  
% 6.56/2.34  
% 6.56/2.34  %Background operators:
% 6.56/2.34  
% 6.56/2.34  
% 6.56/2.34  %Foreground operators:
% 6.56/2.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.56/2.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.56/2.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.56/2.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.56/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.56/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.56/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.56/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.56/2.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.56/2.34  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 6.56/2.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.56/2.34  tff('#skF_2', type, '#skF_2': $i).
% 6.56/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.56/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.56/2.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.56/2.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.56/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.56/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.56/2.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.56/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.56/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.56/2.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.56/2.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.56/2.34  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.56/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.56/2.34  
% 6.56/2.36  tff(f_182, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.56/2.36  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.56/2.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.56/2.36  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.56/2.36  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.56/2.36  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.56/2.36  tff(f_73, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 6.56/2.36  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.56/2.36  tff(f_153, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.56/2.36  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.56/2.37  tff(f_64, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 6.56/2.37  tff(f_165, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.56/2.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.56/2.37  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.56/2.37  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 6.56/2.37  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 6.56/2.37  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.56/2.37  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.56/2.37  tff(c_90, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.56/2.37  tff(c_5101, plain, (![C_199, A_200, B_201]: (v1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.56/2.37  tff(c_5113, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_5101])).
% 6.56/2.37  tff(c_94, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.56/2.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.56/2.37  tff(c_88, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.56/2.37  tff(c_86, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.56/2.37  tff(c_5320, plain, (![A_217, B_218, C_219]: (k2_relset_1(A_217, B_218, C_219)=k2_relat_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.56/2.37  tff(c_5326, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_5320])).
% 6.56/2.37  tff(c_5333, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_5326])).
% 6.56/2.37  tff(c_50, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.56/2.37  tff(c_337, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.56/2.37  tff(c_345, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_337])).
% 6.56/2.37  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.56/2.37  tff(c_524, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.56/2.37  tff(c_527, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_524])).
% 6.56/2.37  tff(c_533, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_527])).
% 6.56/2.37  tff(c_30, plain, (![A_12]: (k1_relat_1(A_12)=k1_xboole_0 | k2_relat_1(A_12)!=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.56/2.37  tff(c_354, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_345, c_30])).
% 6.56/2.37  tff(c_364, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_354])).
% 6.56/2.37  tff(c_547, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_364])).
% 6.56/2.37  tff(c_92, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.56/2.37  tff(c_536, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.56/2.37  tff(c_544, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_536])).
% 6.56/2.37  tff(c_1161, plain, (![B_111, A_112, C_113]: (k1_xboole_0=B_111 | k1_relset_1(A_112, B_111, C_113)=A_112 | ~v1_funct_2(C_113, A_112, B_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.56/2.37  tff(c_1167, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_90, c_1161])).
% 6.56/2.37  tff(c_1175, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_544, c_1167])).
% 6.56/2.37  tff(c_1176, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_547, c_1175])).
% 6.56/2.37  tff(c_48, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.56/2.37  tff(c_46, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.56/2.37  tff(c_396, plain, (![A_71]: (k1_relat_1(k2_funct_1(A_71))=k2_relat_1(A_71) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.56/2.37  tff(c_24, plain, (![A_11]: (~v1_xboole_0(k1_relat_1(A_11)) | ~v1_relat_1(A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.56/2.37  tff(c_1977, plain, (![A_140]: (~v1_xboole_0(k2_relat_1(A_140)) | ~v1_relat_1(k2_funct_1(A_140)) | v1_xboole_0(k2_funct_1(A_140)) | ~v2_funct_1(A_140) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(superposition, [status(thm), theory('equality')], [c_396, c_24])).
% 6.56/2.37  tff(c_1983, plain, (~v1_xboole_0('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | v1_xboole_0(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_533, c_1977])).
% 6.56/2.37  tff(c_1996, plain, (~v1_xboole_0('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | v1_xboole_0(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_94, c_88, c_1983])).
% 6.56/2.37  tff(c_2001, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1996])).
% 6.56/2.37  tff(c_2004, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_2001])).
% 6.56/2.37  tff(c_2008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_345, c_94, c_2004])).
% 6.56/2.37  tff(c_2010, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1996])).
% 6.56/2.37  tff(c_44, plain, (![A_16]: (v1_funct_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.56/2.37  tff(c_84, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.56/2.37  tff(c_228, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_84])).
% 6.56/2.37  tff(c_231, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_228])).
% 6.56/2.37  tff(c_234, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_231])).
% 6.56/2.37  tff(c_278, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.56/2.37  tff(c_281, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_278])).
% 6.56/2.37  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_281])).
% 6.56/2.37  tff(c_291, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_84])).
% 6.56/2.37  tff(c_869, plain, (![B_103, A_104]: (m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_103), A_104))) | ~r1_tarski(k2_relat_1(B_103), A_104) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.56/2.37  tff(c_4726, plain, (![A_182, A_183]: (m1_subset_1(k2_funct_1(A_182), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_182), A_183))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_182)), A_183) | ~v1_funct_1(k2_funct_1(A_182)) | ~v1_relat_1(k2_funct_1(A_182)) | ~v2_funct_1(A_182) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(superposition, [status(thm), theory('equality')], [c_50, c_869])).
% 6.56/2.37  tff(c_4777, plain, (![A_183]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_183))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_183) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_4726])).
% 6.56/2.37  tff(c_4809, plain, (![A_184]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_184))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_184))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_94, c_88, c_2010, c_291, c_4777])).
% 6.56/2.37  tff(c_290, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_84])).
% 6.56/2.37  tff(c_320, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_290])).
% 6.56/2.37  tff(c_4844, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_4809, c_320])).
% 6.56/2.37  tff(c_4850, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_4844])).
% 6.56/2.37  tff(c_4855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_345, c_94, c_88, c_10, c_1176, c_4850])).
% 6.56/2.37  tff(c_4856, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_354])).
% 6.56/2.37  tff(c_4861, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4856, c_24])).
% 6.56/2.37  tff(c_4865, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_2, c_4861])).
% 6.56/2.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.56/2.37  tff(c_4881, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4865, c_4])).
% 6.56/2.37  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.56/2.37  tff(c_4896, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_4881, c_14])).
% 6.56/2.37  tff(c_129, plain, (![A_41]: (v1_xboole_0(k4_relat_1(A_41)) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.56/2.37  tff(c_139, plain, (![A_41]: (k4_relat_1(A_41)=k1_xboole_0 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_129, c_4])).
% 6.56/2.37  tff(c_4880, plain, (k4_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4865, c_139])).
% 6.56/2.37  tff(c_4937, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4881, c_4880])).
% 6.56/2.37  tff(c_4926, plain, (![A_186]: (k4_relat_1(A_186)=k2_funct_1(A_186) | ~v2_funct_1(A_186) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.56/2.37  tff(c_4932, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_4926])).
% 6.56/2.37  tff(c_4936, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_94, c_4932])).
% 6.56/2.37  tff(c_4959, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4937, c_4936])).
% 6.56/2.37  tff(c_4960, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4959, c_320])).
% 6.56/2.37  tff(c_5083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4896, c_4960])).
% 6.56/2.37  tff(c_5084, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_290])).
% 6.56/2.37  tff(c_5085, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_290])).
% 6.56/2.37  tff(c_5336, plain, (![A_220, B_221, C_222]: (k1_relset_1(A_220, B_221, C_222)=k1_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.56/2.37  tff(c_5347, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5085, c_5336])).
% 6.56/2.37  tff(c_5925, plain, (![B_250, C_251, A_252]: (k1_xboole_0=B_250 | v1_funct_2(C_251, A_252, B_250) | k1_relset_1(A_252, B_250, C_251)!=A_252 | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_252, B_250))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.56/2.37  tff(c_5931, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_5085, c_5925])).
% 6.56/2.37  tff(c_5941, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5347, c_5931])).
% 6.56/2.37  tff(c_5942, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5084, c_5941])).
% 6.56/2.37  tff(c_5948, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_5942])).
% 6.56/2.37  tff(c_5951, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_5948])).
% 6.56/2.37  tff(c_5954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5113, c_94, c_88, c_5333, c_5951])).
% 6.56/2.37  tff(c_5955, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5942])).
% 6.56/2.37  tff(c_5122, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_5113, c_30])).
% 6.56/2.37  tff(c_5132, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5122])).
% 6.56/2.37  tff(c_5351, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5333, c_5132])).
% 6.56/2.37  tff(c_5970, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5955, c_5351])).
% 6.56/2.37  tff(c_32, plain, (![A_12]: (k2_relat_1(A_12)=k1_xboole_0 | k1_relat_1(A_12)!=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.56/2.37  tff(c_5123, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_5113, c_32])).
% 6.56/2.37  tff(c_5133, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_5132, c_5123])).
% 6.56/2.37  tff(c_5978, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5955, c_5133])).
% 6.56/2.37  tff(c_5348, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_5336])).
% 6.56/2.37  tff(c_76, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.56/2.37  tff(c_6014, plain, (![B_253, A_254, C_255]: (B_253='#skF_1' | k1_relset_1(A_254, B_253, C_255)=A_254 | ~v1_funct_2(C_255, A_254, B_253) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_254, B_253))))), inference(demodulation, [status(thm), theory('equality')], [c_5955, c_76])).
% 6.56/2.37  tff(c_6023, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_90, c_6014])).
% 6.56/2.37  tff(c_6029, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_5348, c_6023])).
% 6.56/2.37  tff(c_6030, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_5978, c_6029])).
% 6.56/2.37  tff(c_6032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5970, c_6030])).
% 6.56/2.37  tff(c_6033, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5122])).
% 6.56/2.37  tff(c_6102, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6033, c_24])).
% 6.56/2.37  tff(c_6106, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5113, c_2, c_6102])).
% 6.56/2.37  tff(c_6121, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6106, c_4])).
% 6.56/2.37  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.56/2.37  tff(c_6137, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_6121, c_12])).
% 6.56/2.37  tff(c_6034, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5122])).
% 6.56/2.37  tff(c_6151, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6121, c_6034])).
% 6.56/2.37  tff(c_6039, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6033, c_24])).
% 6.56/2.37  tff(c_6043, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5113, c_2, c_6039])).
% 6.56/2.37  tff(c_6058, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6043, c_4])).
% 6.56/2.37  tff(c_6035, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5123])).
% 6.56/2.37  tff(c_6094, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6058, c_6035])).
% 6.56/2.37  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.56/2.37  tff(c_6076, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6058, c_6058, c_28])).
% 6.56/2.37  tff(c_6096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6094, c_6076])).
% 6.56/2.37  tff(c_6098, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5123])).
% 6.56/2.37  tff(c_6158, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6121, c_6098])).
% 6.56/2.37  tff(c_6488, plain, (![B_292, A_293]: (v1_funct_2(B_292, k1_relat_1(B_292), A_293) | ~r1_tarski(k2_relat_1(B_292), A_293) | ~v1_funct_1(B_292) | ~v1_relat_1(B_292))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.56/2.37  tff(c_6497, plain, (![A_293]: (v1_funct_2('#skF_3', '#skF_3', A_293) | ~r1_tarski(k2_relat_1('#skF_3'), A_293) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6158, c_6488])).
% 6.56/2.37  tff(c_6499, plain, (![A_293]: (v1_funct_2('#skF_3', '#skF_3', A_293))), inference(demodulation, [status(thm), theory('equality')], [c_5113, c_94, c_6137, c_6151, c_6497])).
% 6.56/2.37  tff(c_6135, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_6121, c_14])).
% 6.56/2.37  tff(c_6453, plain, (![A_282, B_283, C_284]: (k2_relset_1(A_282, B_283, C_284)=k2_relat_1(C_284) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.56/2.37  tff(c_6457, plain, (![A_282, B_283]: (k2_relset_1(A_282, B_283, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6135, c_6453])).
% 6.56/2.37  tff(c_6459, plain, (![A_282, B_283]: (k2_relset_1(A_282, B_283, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6151, c_6457])).
% 6.56/2.37  tff(c_6460, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6459, c_86])).
% 6.56/2.37  tff(c_6120, plain, (k4_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6106, c_139])).
% 6.56/2.37  tff(c_6174, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6121, c_6120])).
% 6.56/2.37  tff(c_6281, plain, (![A_271]: (k4_relat_1(A_271)=k2_funct_1(A_271) | ~v2_funct_1(A_271) | ~v1_funct_1(A_271) | ~v1_relat_1(A_271))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.56/2.37  tff(c_6287, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_6281])).
% 6.56/2.37  tff(c_6291, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5113, c_94, c_6174, c_6287])).
% 6.56/2.37  tff(c_6295, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6291, c_5084])).
% 6.56/2.37  tff(c_6468, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6460, c_6295])).
% 6.56/2.37  tff(c_6502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6499, c_6468])).
% 6.56/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.37  
% 6.56/2.37  Inference rules
% 6.56/2.37  ----------------------
% 6.56/2.37  #Ref     : 0
% 6.56/2.37  #Sup     : 1505
% 6.56/2.37  #Fact    : 0
% 6.56/2.37  #Define  : 0
% 6.56/2.37  #Split   : 13
% 6.56/2.37  #Chain   : 0
% 6.56/2.37  #Close   : 0
% 6.56/2.37  
% 6.56/2.37  Ordering : KBO
% 6.56/2.37  
% 6.56/2.37  Simplification rules
% 6.56/2.37  ----------------------
% 6.56/2.37  #Subsume      : 236
% 6.56/2.37  #Demod        : 2029
% 6.56/2.37  #Tautology    : 848
% 6.56/2.37  #SimpNegUnit  : 24
% 6.56/2.37  #BackRed      : 109
% 6.56/2.37  
% 6.56/2.37  #Partial instantiations: 0
% 6.56/2.37  #Strategies tried      : 1
% 6.56/2.37  
% 6.56/2.37  Timing (in seconds)
% 6.56/2.37  ----------------------
% 6.93/2.37  Preprocessing        : 0.37
% 6.93/2.37  Parsing              : 0.20
% 6.93/2.37  CNF conversion       : 0.02
% 6.93/2.37  Main loop            : 1.20
% 6.93/2.37  Inferencing          : 0.37
% 6.93/2.37  Reduction            : 0.43
% 6.93/2.37  Demodulation         : 0.30
% 6.93/2.37  BG Simplification    : 0.05
% 6.93/2.37  Subsumption          : 0.27
% 6.93/2.37  Abstraction          : 0.06
% 6.93/2.37  MUC search           : 0.00
% 6.93/2.37  Cooper               : 0.00
% 6.93/2.37  Total                : 1.63
% 6.93/2.37  Index Insertion      : 0.00
% 6.93/2.37  Index Deletion       : 0.00
% 6.93/2.37  Index Matching       : 0.00
% 6.93/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
