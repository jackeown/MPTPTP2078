%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:53 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :  145 (1788 expanded)
%              Number of leaves         :   25 ( 583 expanded)
%              Depth                    :   15
%              Number of atoms          :  253 (4846 expanded)
%              Number of equality atoms :   94 (1159 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2432,plain,(
    ! [C_256,A_257,B_258] :
      ( m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ r1_tarski(k2_relat_1(C_256),B_258)
      | ~ r1_tarski(k1_relat_1(C_256),A_257)
      | ~ v1_relat_1(C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44])).

tff(c_94,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_301,plain,(
    ! [C_67,A_68,B_69] :
      ( m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ r1_tarski(k2_relat_1(C_67),B_69)
      | ~ r1_tarski(k1_relat_1(C_67),A_68)
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1536,plain,(
    ! [C_173,A_174,B_175] :
      ( r1_tarski(C_173,k2_zfmisc_1(A_174,B_175))
      | ~ r1_tarski(k2_relat_1(C_173),B_175)
      | ~ r1_tarski(k1_relat_1(C_173),A_174)
      | ~ v1_relat_1(C_173) ) ),
    inference(resolution,[status(thm)],[c_301,c_16])).

tff(c_1541,plain,(
    ! [A_174] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_174,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_174)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_1536])).

tff(c_1550,plain,(
    ! [A_176] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_176,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1541])).

tff(c_1560,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1550])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_195,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_210,plain,(
    ! [A_47,B_48,A_6] :
      ( k1_relset_1(A_47,B_48,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_47,B_48)) ) ),
    inference(resolution,[status(thm)],[c_18,c_195])).

tff(c_1590,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1560,c_210])).

tff(c_1412,plain,(
    ! [B_158,C_159,A_160] :
      ( k1_xboole_0 = B_158
      | v1_funct_2(C_159,A_160,B_158)
      | k1_relset_1(A_160,B_158,C_159) != A_160
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1808,plain,(
    ! [B_198,A_199,A_200] :
      ( k1_xboole_0 = B_198
      | v1_funct_2(A_199,A_200,B_198)
      | k1_relset_1(A_200,B_198,A_199) != A_200
      | ~ r1_tarski(A_199,k2_zfmisc_1(A_200,B_198)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1412])).

tff(c_1814,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1560,c_1808])).

tff(c_1831,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1590,c_1814])).

tff(c_1832,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1831])).

tff(c_375,plain,(
    ! [C_82,A_83,B_84] :
      ( r1_tarski(C_82,k2_zfmisc_1(A_83,B_84))
      | ~ r1_tarski(k2_relat_1(C_82),B_84)
      | ~ r1_tarski(k1_relat_1(C_82),A_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_301,c_16])).

tff(c_380,plain,(
    ! [A_83] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_83,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_83)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_375])).

tff(c_389,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_85,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_380])).

tff(c_399,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_389])).

tff(c_408,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_399,c_210])).

tff(c_487,plain,(
    ! [B_95,C_96,A_97] :
      ( k1_xboole_0 = B_95
      | v1_funct_2(C_96,A_97,B_95)
      | k1_relset_1(A_97,B_95,C_96) != A_97
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_582,plain,(
    ! [B_106,A_107,A_108] :
      ( k1_xboole_0 = B_106
      | v1_funct_2(A_107,A_108,B_106)
      | k1_relset_1(A_108,B_106,A_107) != A_108
      | ~ r1_tarski(A_107,k2_zfmisc_1(A_108,B_106)) ) ),
    inference(resolution,[status(thm)],[c_18,c_487])).

tff(c_588,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_399,c_582])).

tff(c_605,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_588])).

tff(c_606,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_605])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_640,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_606,c_12])).

tff(c_670,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_399])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_774,plain,(
    ! [A_116] :
      ( A_116 = '#skF_1'
      | ~ r1_tarski(A_116,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_606,c_8])).

tff(c_785,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_670,c_774])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_411,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_399,c_2])).

tff(c_437,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_669,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_437])).

tff(c_799,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_669])).

tff(c_810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_799])).

tff(c_811,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_268,plain,(
    ! [A_62,B_63,A_64] :
      ( k1_relset_1(A_62,B_63,A_64) = k1_relat_1(A_64)
      | ~ r1_tarski(A_64,k2_zfmisc_1(A_62,B_63)) ) ),
    inference(resolution,[status(thm)],[c_18,c_195])).

tff(c_283,plain,(
    ! [A_62,B_63] : k1_relset_1(A_62,B_63,k2_zfmisc_1(A_62,B_63)) = k1_relat_1(k2_zfmisc_1(A_62,B_63)) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_861,plain,(
    ! [B_122,C_123,A_124] :
      ( k1_xboole_0 = B_122
      | v1_funct_2(C_123,A_124,B_122)
      | k1_relset_1(A_124,B_122,C_123) != A_124
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_995,plain,(
    ! [B_134,A_135,A_136] :
      ( k1_xboole_0 = B_134
      | v1_funct_2(A_135,A_136,B_134)
      | k1_relset_1(A_136,B_134,A_135) != A_136
      | ~ r1_tarski(A_135,k2_zfmisc_1(A_136,B_134)) ) ),
    inference(resolution,[status(thm)],[c_18,c_861])).

tff(c_1014,plain,(
    ! [B_134,A_136] :
      ( k1_xboole_0 = B_134
      | v1_funct_2(k2_zfmisc_1(A_136,B_134),A_136,B_134)
      | k1_relset_1(A_136,B_134,k2_zfmisc_1(A_136,B_134)) != A_136 ) ),
    inference(resolution,[status(thm)],[c_6,c_995])).

tff(c_1055,plain,(
    ! [B_141,A_142] :
      ( k1_xboole_0 = B_141
      | v1_funct_2(k2_zfmisc_1(A_142,B_141),A_142,B_141)
      | k1_relat_1(k2_zfmisc_1(A_142,B_141)) != A_142 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_1014])).

tff(c_1064,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_1055])).

tff(c_1080,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_1064])).

tff(c_1081,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1080])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_839,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = k1_xboole_0
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_10])).

tff(c_860,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_839])).

tff(c_1089,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_860])).

tff(c_1112,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1081,c_12])).

tff(c_1118,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_811])).

tff(c_1121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1089,c_1118])).

tff(c_1123,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_839])).

tff(c_26,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_156,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_159,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_156])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_159])).

tff(c_165,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_232,plain,(
    ! [B_55,C_56] :
      ( k1_relset_1(k1_xboole_0,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_195])).

tff(c_238,plain,(
    ! [B_55] : k1_relset_1(k1_xboole_0,B_55,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_165,c_232])).

tff(c_30,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_329,plain,(
    ! [C_71,B_72] :
      ( v1_funct_2(C_71,k1_xboole_0,B_72)
      | k1_relset_1(k1_xboole_0,B_72,C_71) != k1_xboole_0
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_331,plain,(
    ! [B_72] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_72)
      | k1_relset_1(k1_xboole_0,B_72,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_165,c_329])).

tff(c_336,plain,(
    ! [B_72] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_72)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_331])).

tff(c_338,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_1130,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1123,c_338])).

tff(c_1122,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_839])).

tff(c_1257,plain,
    ( k1_relat_1('#skF_2') = '#skF_2'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1123,c_1122])).

tff(c_1258,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1130,c_1257])).

tff(c_1275,plain,(
    r1_tarski(k2_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_46])).

tff(c_1145,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1123,c_8])).

tff(c_1394,plain,(
    ! [A_157] :
      ( A_157 = '#skF_1'
      | ~ r1_tarski(A_157,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_1258,c_1145])).

tff(c_1402,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1275,c_1394])).

tff(c_128,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_128])).

tff(c_148,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_1273,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_148])).

tff(c_1405,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_1273])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1405])).

tff(c_1411,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_1852,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_1832,c_1411])).

tff(c_1867,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_1832,c_12])).

tff(c_1940,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_1560])).

tff(c_2038,plain,(
    ! [A_211] :
      ( A_211 = '#skF_1'
      | ~ r1_tarski(A_211,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_1832,c_8])).

tff(c_2049,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1940,c_2038])).

tff(c_1512,plain,(
    ! [C_168,B_169] :
      ( m1_subset_1(C_168,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_168),B_169)
      | ~ r1_tarski(k1_relat_1(C_168),k1_xboole_0)
      | ~ v1_relat_1(C_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_301])).

tff(c_1519,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1512])).

tff(c_1526,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1519])).

tff(c_1528,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1526])).

tff(c_1846,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_1528])).

tff(c_2053,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_1846])).

tff(c_2066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1852,c_2053])).

tff(c_2067,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1526])).

tff(c_2086,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2067,c_16])).

tff(c_2104,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2086,c_8])).

tff(c_1410,plain,(
    ! [B_72] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_72) ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_2134,plain,(
    ! [B_72] : v1_funct_2('#skF_2','#skF_2',B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2104,c_2104,c_1410])).

tff(c_2135,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2104,c_2104,c_1411])).

tff(c_2158,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_94])).

tff(c_2186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2134,c_2158])).

tff(c_2187,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_2224,plain,(
    ! [A_218] :
      ( v1_funct_2(A_218,k1_relat_1(A_218),k2_relat_1(A_218))
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2227,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2187,c_2224])).

tff(c_2229,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2227])).

tff(c_2231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2229])).

tff(c_2232,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2441,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2432,c_2232])).

tff(c_2456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6,c_46,c_2441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:31:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.67  
% 3.89/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.67  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.89/1.67  
% 3.89/1.67  %Foreground sorts:
% 3.89/1.67  
% 3.89/1.67  
% 3.89/1.67  %Background operators:
% 3.89/1.67  
% 3.89/1.67  
% 3.89/1.67  %Foreground operators:
% 3.89/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.89/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.89/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.89/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.89/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.89/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.67  
% 4.25/1.70  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.25/1.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.25/1.70  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.25/1.70  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.25/1.70  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.25/1.70  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.25/1.70  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.25/1.70  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.25/1.70  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.25/1.70  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.25/1.70  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.25/1.70  tff(c_46, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.25/1.70  tff(c_2432, plain, (![C_256, A_257, B_258]: (m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~r1_tarski(k2_relat_1(C_256), B_258) | ~r1_tarski(k1_relat_1(C_256), A_257) | ~v1_relat_1(C_256))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.25/1.70  tff(c_48, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.25/1.70  tff(c_44, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.25/1.70  tff(c_52, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44])).
% 4.25/1.70  tff(c_94, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 4.25/1.70  tff(c_301, plain, (![C_67, A_68, B_69]: (m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~r1_tarski(k2_relat_1(C_67), B_69) | ~r1_tarski(k1_relat_1(C_67), A_68) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.25/1.70  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.25/1.70  tff(c_1536, plain, (![C_173, A_174, B_175]: (r1_tarski(C_173, k2_zfmisc_1(A_174, B_175)) | ~r1_tarski(k2_relat_1(C_173), B_175) | ~r1_tarski(k1_relat_1(C_173), A_174) | ~v1_relat_1(C_173))), inference(resolution, [status(thm)], [c_301, c_16])).
% 4.25/1.70  tff(c_1541, plain, (![A_174]: (r1_tarski('#skF_2', k2_zfmisc_1(A_174, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_174) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_1536])).
% 4.25/1.70  tff(c_1550, plain, (![A_176]: (r1_tarski('#skF_2', k2_zfmisc_1(A_176, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_176))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1541])).
% 4.25/1.70  tff(c_1560, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1550])).
% 4.25/1.70  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.25/1.70  tff(c_195, plain, (![A_47, B_48, C_49]: (k1_relset_1(A_47, B_48, C_49)=k1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.25/1.70  tff(c_210, plain, (![A_47, B_48, A_6]: (k1_relset_1(A_47, B_48, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_47, B_48)))), inference(resolution, [status(thm)], [c_18, c_195])).
% 4.25/1.70  tff(c_1590, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1560, c_210])).
% 4.25/1.70  tff(c_1412, plain, (![B_158, C_159, A_160]: (k1_xboole_0=B_158 | v1_funct_2(C_159, A_160, B_158) | k1_relset_1(A_160, B_158, C_159)!=A_160 | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_158))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.25/1.70  tff(c_1808, plain, (![B_198, A_199, A_200]: (k1_xboole_0=B_198 | v1_funct_2(A_199, A_200, B_198) | k1_relset_1(A_200, B_198, A_199)!=A_200 | ~r1_tarski(A_199, k2_zfmisc_1(A_200, B_198)))), inference(resolution, [status(thm)], [c_18, c_1412])).
% 4.25/1.70  tff(c_1814, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1560, c_1808])).
% 4.25/1.70  tff(c_1831, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1590, c_1814])).
% 4.25/1.70  tff(c_1832, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_94, c_1831])).
% 4.25/1.70  tff(c_375, plain, (![C_82, A_83, B_84]: (r1_tarski(C_82, k2_zfmisc_1(A_83, B_84)) | ~r1_tarski(k2_relat_1(C_82), B_84) | ~r1_tarski(k1_relat_1(C_82), A_83) | ~v1_relat_1(C_82))), inference(resolution, [status(thm)], [c_301, c_16])).
% 4.25/1.70  tff(c_380, plain, (![A_83]: (r1_tarski('#skF_2', k2_zfmisc_1(A_83, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_83) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_375])).
% 4.25/1.70  tff(c_389, plain, (![A_85]: (r1_tarski('#skF_2', k2_zfmisc_1(A_85, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_85))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_380])).
% 4.25/1.70  tff(c_399, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_389])).
% 4.25/1.70  tff(c_408, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_399, c_210])).
% 4.25/1.70  tff(c_487, plain, (![B_95, C_96, A_97]: (k1_xboole_0=B_95 | v1_funct_2(C_96, A_97, B_95) | k1_relset_1(A_97, B_95, C_96)!=A_97 | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_95))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.25/1.70  tff(c_582, plain, (![B_106, A_107, A_108]: (k1_xboole_0=B_106 | v1_funct_2(A_107, A_108, B_106) | k1_relset_1(A_108, B_106, A_107)!=A_108 | ~r1_tarski(A_107, k2_zfmisc_1(A_108, B_106)))), inference(resolution, [status(thm)], [c_18, c_487])).
% 4.25/1.70  tff(c_588, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_399, c_582])).
% 4.25/1.70  tff(c_605, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_588])).
% 4.25/1.70  tff(c_606, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_94, c_605])).
% 4.25/1.70  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.25/1.70  tff(c_640, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_606, c_606, c_12])).
% 4.25/1.70  tff(c_670, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_640, c_399])).
% 4.25/1.70  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.25/1.70  tff(c_774, plain, (![A_116]: (A_116='#skF_1' | ~r1_tarski(A_116, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_606, c_606, c_8])).
% 4.25/1.70  tff(c_785, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_670, c_774])).
% 4.25/1.70  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.25/1.70  tff(c_411, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_399, c_2])).
% 4.25/1.70  tff(c_437, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_411])).
% 4.25/1.70  tff(c_669, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_640, c_437])).
% 4.25/1.70  tff(c_799, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_785, c_669])).
% 4.25/1.70  tff(c_810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_799])).
% 4.25/1.70  tff(c_811, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_411])).
% 4.25/1.70  tff(c_268, plain, (![A_62, B_63, A_64]: (k1_relset_1(A_62, B_63, A_64)=k1_relat_1(A_64) | ~r1_tarski(A_64, k2_zfmisc_1(A_62, B_63)))), inference(resolution, [status(thm)], [c_18, c_195])).
% 4.25/1.70  tff(c_283, plain, (![A_62, B_63]: (k1_relset_1(A_62, B_63, k2_zfmisc_1(A_62, B_63))=k1_relat_1(k2_zfmisc_1(A_62, B_63)))), inference(resolution, [status(thm)], [c_6, c_268])).
% 4.25/1.70  tff(c_861, plain, (![B_122, C_123, A_124]: (k1_xboole_0=B_122 | v1_funct_2(C_123, A_124, B_122) | k1_relset_1(A_124, B_122, C_123)!=A_124 | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.25/1.70  tff(c_995, plain, (![B_134, A_135, A_136]: (k1_xboole_0=B_134 | v1_funct_2(A_135, A_136, B_134) | k1_relset_1(A_136, B_134, A_135)!=A_136 | ~r1_tarski(A_135, k2_zfmisc_1(A_136, B_134)))), inference(resolution, [status(thm)], [c_18, c_861])).
% 4.25/1.70  tff(c_1014, plain, (![B_134, A_136]: (k1_xboole_0=B_134 | v1_funct_2(k2_zfmisc_1(A_136, B_134), A_136, B_134) | k1_relset_1(A_136, B_134, k2_zfmisc_1(A_136, B_134))!=A_136)), inference(resolution, [status(thm)], [c_6, c_995])).
% 4.25/1.70  tff(c_1055, plain, (![B_141, A_142]: (k1_xboole_0=B_141 | v1_funct_2(k2_zfmisc_1(A_142, B_141), A_142, B_141) | k1_relat_1(k2_zfmisc_1(A_142, B_141))!=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_283, c_1014])).
% 4.25/1.70  tff(c_1064, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_811, c_1055])).
% 4.25/1.70  tff(c_1080, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_1064])).
% 4.25/1.70  tff(c_1081, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_94, c_1080])).
% 4.25/1.70  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.25/1.70  tff(c_839, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')=k1_xboole_0 | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_811, c_10])).
% 4.25/1.70  tff(c_860, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_839])).
% 4.25/1.70  tff(c_1089, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_860])).
% 4.25/1.70  tff(c_1112, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_1081, c_12])).
% 4.25/1.70  tff(c_1118, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1112, c_811])).
% 4.25/1.70  tff(c_1121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1089, c_1118])).
% 4.25/1.70  tff(c_1123, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_839])).
% 4.25/1.70  tff(c_26, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.25/1.70  tff(c_56, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 4.25/1.70  tff(c_156, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_56])).
% 4.25/1.70  tff(c_159, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_156])).
% 4.25/1.70  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_159])).
% 4.25/1.70  tff(c_165, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_56])).
% 4.25/1.70  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.25/1.70  tff(c_232, plain, (![B_55, C_56]: (k1_relset_1(k1_xboole_0, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_195])).
% 4.25/1.70  tff(c_238, plain, (![B_55]: (k1_relset_1(k1_xboole_0, B_55, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_165, c_232])).
% 4.25/1.70  tff(c_30, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.25/1.70  tff(c_329, plain, (![C_71, B_72]: (v1_funct_2(C_71, k1_xboole_0, B_72) | k1_relset_1(k1_xboole_0, B_72, C_71)!=k1_xboole_0 | ~m1_subset_1(C_71, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 4.25/1.70  tff(c_331, plain, (![B_72]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_72) | k1_relset_1(k1_xboole_0, B_72, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_165, c_329])).
% 4.25/1.70  tff(c_336, plain, (![B_72]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_72) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_238, c_331])).
% 4.25/1.70  tff(c_338, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_336])).
% 4.25/1.70  tff(c_1130, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1123, c_338])).
% 4.25/1.70  tff(c_1122, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_839])).
% 4.25/1.70  tff(c_1257, plain, (k1_relat_1('#skF_2')='#skF_2' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1123, c_1122])).
% 4.25/1.70  tff(c_1258, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1130, c_1257])).
% 4.25/1.70  tff(c_1275, plain, (r1_tarski(k2_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_46])).
% 4.25/1.70  tff(c_1145, plain, (![A_3]: (A_3='#skF_2' | ~r1_tarski(A_3, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1123, c_8])).
% 4.25/1.70  tff(c_1394, plain, (![A_157]: (A_157='#skF_1' | ~r1_tarski(A_157, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_1258, c_1145])).
% 4.25/1.70  tff(c_1402, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1275, c_1394])).
% 4.25/1.70  tff(c_128, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.25/1.70  tff(c_133, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_128])).
% 4.25/1.70  tff(c_148, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_133])).
% 4.25/1.70  tff(c_1273, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_148])).
% 4.25/1.70  tff(c_1405, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_1273])).
% 4.25/1.70  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1405])).
% 4.25/1.70  tff(c_1411, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_336])).
% 4.25/1.70  tff(c_1852, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1832, c_1832, c_1411])).
% 4.25/1.70  tff(c_1867, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1832, c_1832, c_12])).
% 4.25/1.70  tff(c_1940, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_1560])).
% 4.25/1.70  tff(c_2038, plain, (![A_211]: (A_211='#skF_1' | ~r1_tarski(A_211, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1832, c_1832, c_8])).
% 4.25/1.70  tff(c_2049, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_1940, c_2038])).
% 4.25/1.70  tff(c_1512, plain, (![C_168, B_169]: (m1_subset_1(C_168, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_168), B_169) | ~r1_tarski(k1_relat_1(C_168), k1_xboole_0) | ~v1_relat_1(C_168))), inference(superposition, [status(thm), theory('equality')], [c_14, c_301])).
% 4.25/1.70  tff(c_1519, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_1512])).
% 4.25/1.70  tff(c_1526, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1519])).
% 4.25/1.70  tff(c_1528, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1526])).
% 4.25/1.70  tff(c_1846, plain, (~r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1832, c_1528])).
% 4.25/1.70  tff(c_2053, plain, (~r1_tarski(k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_1846])).
% 4.25/1.70  tff(c_2066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1852, c_2053])).
% 4.25/1.70  tff(c_2067, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1526])).
% 4.25/1.70  tff(c_2086, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_2067, c_16])).
% 4.25/1.70  tff(c_2104, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2086, c_8])).
% 4.25/1.70  tff(c_1410, plain, (![B_72]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_72))), inference(splitRight, [status(thm)], [c_336])).
% 4.25/1.70  tff(c_2134, plain, (![B_72]: (v1_funct_2('#skF_2', '#skF_2', B_72))), inference(demodulation, [status(thm), theory('equality')], [c_2104, c_2104, c_1410])).
% 4.25/1.70  tff(c_2135, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2104, c_2104, c_1411])).
% 4.25/1.70  tff(c_2158, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2135, c_94])).
% 4.25/1.70  tff(c_2186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2134, c_2158])).
% 4.25/1.70  tff(c_2187, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_133])).
% 4.25/1.70  tff(c_2224, plain, (![A_218]: (v1_funct_2(A_218, k1_relat_1(A_218), k2_relat_1(A_218)) | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.25/1.70  tff(c_2227, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2187, c_2224])).
% 4.25/1.70  tff(c_2229, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2227])).
% 4.25/1.70  tff(c_2231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_2229])).
% 4.25/1.70  tff(c_2232, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_52])).
% 4.25/1.70  tff(c_2441, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2432, c_2232])).
% 4.25/1.70  tff(c_2456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_6, c_46, c_2441])).
% 4.25/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/1.70  
% 4.25/1.70  Inference rules
% 4.25/1.70  ----------------------
% 4.25/1.70  #Ref     : 0
% 4.25/1.70  #Sup     : 501
% 4.25/1.70  #Fact    : 0
% 4.25/1.70  #Define  : 0
% 4.25/1.70  #Split   : 16
% 4.25/1.70  #Chain   : 0
% 4.25/1.70  #Close   : 0
% 4.25/1.70  
% 4.25/1.70  Ordering : KBO
% 4.25/1.70  
% 4.25/1.70  Simplification rules
% 4.25/1.70  ----------------------
% 4.25/1.70  #Subsume      : 71
% 4.25/1.70  #Demod        : 641
% 4.25/1.70  #Tautology    : 223
% 4.25/1.70  #SimpNegUnit  : 11
% 4.25/1.70  #BackRed      : 200
% 4.25/1.70  
% 4.25/1.70  #Partial instantiations: 0
% 4.25/1.70  #Strategies tried      : 1
% 4.25/1.70  
% 4.25/1.70  Timing (in seconds)
% 4.25/1.70  ----------------------
% 4.25/1.70  Preprocessing        : 0.31
% 4.25/1.70  Parsing              : 0.16
% 4.25/1.70  CNF conversion       : 0.02
% 4.25/1.70  Main loop            : 0.61
% 4.25/1.70  Inferencing          : 0.21
% 4.25/1.70  Reduction            : 0.20
% 4.25/1.70  Demodulation         : 0.14
% 4.25/1.70  BG Simplification    : 0.03
% 4.25/1.70  Subsumption          : 0.12
% 4.25/1.70  Abstraction          : 0.03
% 4.25/1.70  MUC search           : 0.00
% 4.25/1.70  Cooper               : 0.00
% 4.25/1.70  Total                : 0.97
% 4.25/1.70  Index Insertion      : 0.00
% 4.25/1.70  Index Deletion       : 0.00
% 4.25/1.70  Index Matching       : 0.00
% 4.25/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
