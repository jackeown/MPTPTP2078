%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:55 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  204 (3963 expanded)
%              Number of leaves         :   43 (1275 expanded)
%              Depth                    :   20
%              Number of atoms          :  357 (10801 expanded)
%              Number of equality atoms :  139 (3511 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_48,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_295,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_relset_1(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_304,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_295])).

tff(c_44,plain,(
    ! [A_27] : k6_relat_1(A_27) = k6_partfun1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [A_4] : k2_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_40,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_124,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_153,plain,(
    ! [A_53] : v1_relat_1(k6_partfun1(A_53)) ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_6,plain,(
    ! [A_3] :
      ( k2_relat_1(A_3) != k1_xboole_0
      | k1_xboole_0 = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_159,plain,(
    ! [A_53] :
      ( k2_relat_1(k6_partfun1(A_53)) != k1_xboole_0
      | k6_partfun1(A_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_6])).

tff(c_181,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | k6_partfun1(A_58) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_159])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_192,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_54])).

tff(c_246,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_70,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_68,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_135,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_124])).

tff(c_164,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_175,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_164])).

tff(c_311,plain,(
    ! [B_76,A_77] :
      ( k2_relat_1(B_76) = A_77
      | ~ v2_funct_2(B_76,A_77)
      | ~ v5_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_323,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_175,c_311])).

tff(c_335,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_323])).

tff(c_654,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_66,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_795,plain,(
    ! [C_117,B_118,A_119] :
      ( v2_funct_2(C_117,B_118)
      | ~ v3_funct_2(C_117,A_119,B_118)
      | ~ v1_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_801,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_795])).

tff(c_809,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_801])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_654,c_809])).

tff(c_812,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_825,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_831,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_825])).

tff(c_838,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_831])).

tff(c_935,plain,(
    ! [C_128,A_129,B_130] :
      ( v2_funct_1(C_128)
      | ~ v3_funct_2(C_128,A_129,B_130)
      | ~ v1_funct_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_941,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_935])).

tff(c_948,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_941])).

tff(c_1440,plain,(
    ! [C_164,D_165,B_166,A_167] :
      ( k2_funct_1(C_164) = D_165
      | k1_xboole_0 = B_166
      | k1_xboole_0 = A_167
      | ~ v2_funct_1(C_164)
      | ~ r2_relset_1(A_167,A_167,k1_partfun1(A_167,B_166,B_166,A_167,C_164,D_165),k6_partfun1(A_167))
      | k2_relset_1(A_167,B_166,C_164) != B_166
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(B_166,A_167)))
      | ~ v1_funct_2(D_165,B_166,A_167)
      | ~ v1_funct_1(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166)))
      | ~ v1_funct_2(C_164,A_167,B_166)
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1452,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1440])).

tff(c_1455,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_56,c_838,c_948,c_1452])).

tff(c_1456,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_1455])).

tff(c_1134,plain,(
    ! [A_147,B_148] :
      ( k2_funct_2(A_147,B_148) = k2_funct_1(B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_zfmisc_1(A_147,A_147)))
      | ~ v3_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1140,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1134])).

tff(c_1148,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1140])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1152,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_52])).

tff(c_1457,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1152])).

tff(c_1461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_1457])).

tff(c_1463,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_144,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_135,c_6])).

tff(c_178,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_1467,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1463,c_178])).

tff(c_1578,plain,(
    ! [B_180,A_181] :
      ( k2_relat_1(B_180) = A_181
      | ~ v2_funct_2(B_180,A_181)
      | ~ v5_relat_1(B_180,A_181)
      | ~ v1_relat_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1590,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_175,c_1578])).

tff(c_1603,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_1590])).

tff(c_1604,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1467,c_1603])).

tff(c_1724,plain,(
    ! [C_195,B_196,A_197] :
      ( v2_funct_2(C_195,B_196)
      | ~ v3_funct_2(C_195,A_197,B_196)
      | ~ v1_funct_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1730,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1724])).

tff(c_1738,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1730])).

tff(c_1740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1604,c_1738])).

tff(c_1741,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_163,plain,(
    ! [A_53] :
      ( k1_xboole_0 != A_53
      | k6_partfun1(A_53) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_159])).

tff(c_1786,plain,(
    ! [A_203] :
      ( A_203 != '#skF_2'
      | k6_partfun1(A_203) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1741,c_163])).

tff(c_1800,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_54])).

tff(c_1857,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1800])).

tff(c_1742,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_1754,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1742])).

tff(c_1943,plain,(
    ! [B_215,A_216] :
      ( k2_relat_1(B_215) = A_216
      | ~ v2_funct_2(B_215,A_216)
      | ~ v5_relat_1(B_215,A_216)
      | ~ v1_relat_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1955,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_175,c_1943])).

tff(c_1967,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_1754,c_1955])).

tff(c_1968,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1857,c_1967])).

tff(c_2083,plain,(
    ! [C_233,B_234,A_235] :
      ( v2_funct_2(C_233,B_234)
      | ~ v3_funct_2(C_233,A_235,B_234)
      | ~ v1_funct_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_235,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2089,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2083])).

tff(c_2097,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2089])).

tff(c_2099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1968,c_2097])).

tff(c_2101,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1800])).

tff(c_136,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_152,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_136,c_6])).

tff(c_1767,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1741,c_152])).

tff(c_1768,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1767])).

tff(c_2108,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2101,c_1768])).

tff(c_176,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_164])).

tff(c_2133,plain,(
    ! [B_236,A_237] :
      ( k2_relat_1(B_236) = A_237
      | ~ v2_funct_2(B_236,A_237)
      | ~ v5_relat_1(B_236,A_237)
      | ~ v1_relat_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2139,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_2133])).

tff(c_2145,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2139])).

tff(c_2298,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2108,c_2145])).

tff(c_58,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2404,plain,(
    ! [C_262,B_263,A_264] :
      ( v2_funct_2(C_262,B_263)
      | ~ v3_funct_2(C_262,A_264,B_263)
      | ~ v1_funct_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_264,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2413,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2404])).

tff(c_2421,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2413])).

tff(c_2423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2298,c_2421])).

tff(c_2424,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1767])).

tff(c_2430,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_1741])).

tff(c_10,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_73,plain,(
    ! [A_4] : k1_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_relat_1(A_3) != k1_xboole_0
      | k1_xboole_0 = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_156,plain,(
    ! [A_53] :
      ( k1_relat_1(k6_partfun1(A_53)) != k1_xboole_0
      | k6_partfun1(A_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_8])).

tff(c_161,plain,(
    ! [A_53] :
      ( k1_xboole_0 != A_53
      | k6_partfun1(A_53) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_156])).

tff(c_2480,plain,(
    ! [A_270] :
      ( A_270 != '#skF_3'
      | k6_partfun1(A_270) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2430,c_2430,c_161])).

tff(c_2519,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_73])).

tff(c_151,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_136,c_8])).

tff(c_1759,plain,
    ( k1_relat_1('#skF_3') != '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1741,c_151])).

tff(c_1760,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1759])).

tff(c_2427,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_1760])).

tff(c_2522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_2427])).

tff(c_2523,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1759])).

tff(c_2527,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_1741])).

tff(c_2594,plain,(
    ! [A_53] :
      ( A_53 != '#skF_3'
      | k6_partfun1(A_53) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2527,c_2527,c_163])).

tff(c_2530,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_54])).

tff(c_2636,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),'#skF_3')
    | '#skF_3' != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2594,c_2530])).

tff(c_2663,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2636])).

tff(c_2525,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_2523,c_1754])).

tff(c_2720,plain,(
    ! [B_287,A_288] :
      ( k2_relat_1(B_287) = A_288
      | ~ v2_funct_2(B_287,A_288)
      | ~ v5_relat_1(B_287,A_288)
      | ~ v1_relat_1(B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2729,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_2720])).

tff(c_2738,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2525,c_2729])).

tff(c_2739,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2663,c_2738])).

tff(c_2818,plain,(
    ! [C_302,B_303,A_304] :
      ( v2_funct_2(C_302,B_303)
      | ~ v3_funct_2(C_302,A_304,B_303)
      | ~ v1_funct_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_304,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2824,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2818])).

tff(c_2829,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2824])).

tff(c_2831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2739,c_2829])).

tff(c_2833,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2636])).

tff(c_2596,plain,(
    ! [A_278] :
      ( A_278 != '#skF_3'
      | k6_partfun1(A_278) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2527,c_2527,c_163])).

tff(c_2613,plain,(
    ! [A_278] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_278,A_278)))
      | A_278 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2596,c_40])).

tff(c_3243,plain,(
    ! [A_341] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_341,A_341)))
      | A_341 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2833,c_2613])).

tff(c_24,plain,(
    ! [A_15,B_16,D_18] :
      ( r2_relset_1(A_15,B_16,D_18,D_18)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3293,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3243,c_24])).

tff(c_2852,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_60])).

tff(c_2853,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_58])).

tff(c_2854,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_62])).

tff(c_14,plain,(
    ! [A_5] : k2_funct_1(k6_relat_1(A_5)) = k6_relat_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ! [A_5] : k2_funct_1(k6_partfun1(A_5)) = k6_partfun1(A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_14])).

tff(c_2616,plain,(
    ! [A_278] :
      ( k6_partfun1(A_278) = k2_funct_1('#skF_3')
      | A_278 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2596,c_71])).

tff(c_3024,plain,(
    ! [A_320] :
      ( k6_partfun1(A_320) = k2_funct_1('#skF_1')
      | A_320 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2833,c_2616])).

tff(c_3104,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3024,c_72])).

tff(c_134,plain,(
    ! [A_24] : v1_relat_1(k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_3044,plain,(
    ! [A_320] :
      ( v1_relat_1(k2_funct_1('#skF_1'))
      | A_320 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3024,c_134])).

tff(c_3068,plain,(
    ! [A_320] : A_320 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3044])).

tff(c_2844,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2833,c_2525])).

tff(c_2851,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_56])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2949,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2851,c_22])).

tff(c_2962,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_2949])).

tff(c_3089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3068,c_2962])).

tff(c_3090,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3044])).

tff(c_2848,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2523])).

tff(c_1744,plain,(
    ! [A_3] :
      ( k2_relat_1(A_3) != '#skF_2'
      | A_3 = '#skF_2'
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_1741,c_6])).

tff(c_3157,plain,(
    ! [A_334] :
      ( k2_relat_1(A_334) != '#skF_1'
      | A_334 = '#skF_1'
      | ~ v1_relat_1(A_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_2848,c_1744])).

tff(c_3160,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3090,c_3157])).

tff(c_3169,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3104,c_3160])).

tff(c_3240,plain,(
    ! [A_278] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_278,A_278)))
      | A_278 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2833,c_2613])).

tff(c_3301,plain,(
    ! [A_344,B_345] :
      ( k2_funct_2(A_344,B_345) = k2_funct_1(B_345)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(k2_zfmisc_1(A_344,A_344)))
      | ~ v3_funct_2(B_345,A_344,A_344)
      | ~ v1_funct_2(B_345,A_344,A_344)
      | ~ v1_funct_1(B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3304,plain,(
    ! [A_278] :
      ( k2_funct_2(A_278,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_278,A_278)
      | ~ v1_funct_2('#skF_1',A_278,A_278)
      | ~ v1_funct_1('#skF_1')
      | A_278 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3240,c_3301])).

tff(c_3352,plain,(
    ! [A_354] :
      ( k2_funct_2(A_354,'#skF_1') = '#skF_1'
      | ~ v3_funct_2('#skF_1',A_354,A_354)
      | ~ v1_funct_2('#skF_1',A_354,A_354)
      | A_354 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2854,c_3169,c_3304])).

tff(c_3355,plain,
    ( k2_funct_2('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2853,c_3352])).

tff(c_3358,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2852,c_3355])).

tff(c_2531,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_52])).

tff(c_2843,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2833,c_2531])).

tff(c_3359,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_2843])).

tff(c_3362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3293,c_3359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.94  
% 4.88/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.95  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.88/1.95  
% 4.88/1.95  %Foreground sorts:
% 4.88/1.95  
% 4.88/1.95  
% 4.88/1.95  %Background operators:
% 4.88/1.95  
% 4.88/1.95  
% 4.88/1.95  %Foreground operators:
% 4.88/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.88/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.88/1.95  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.88/1.95  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.88/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.95  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.88/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/1.95  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.88/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.88/1.95  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.88/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.88/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.88/1.95  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.88/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.88/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.95  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.88/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.88/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.88/1.95  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.88/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.88/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.88/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.88/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.88/1.95  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.88/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.88/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.88/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.88/1.95  
% 4.88/1.97  tff(f_172, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 4.88/1.97  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.88/1.97  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.88/1.97  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.88/1.97  tff(f_94, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.88/1.97  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.88/1.97  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.88/1.97  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.88/1.97  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.88/1.97  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.88/1.97  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.88/1.97  tff(f_150, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.88/1.97  tff(f_104, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.88/1.97  tff(f_48, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 4.88/1.97  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_295, plain, (![A_72, B_73, D_74]: (r2_relset_1(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.88/1.97  tff(c_304, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_295])).
% 4.88/1.97  tff(c_44, plain, (![A_27]: (k6_relat_1(A_27)=k6_partfun1(A_27))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.88/1.97  tff(c_12, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.88/1.97  tff(c_72, plain, (![A_4]: (k2_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 4.88/1.97  tff(c_40, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.88/1.97  tff(c_124, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.88/1.97  tff(c_153, plain, (![A_53]: (v1_relat_1(k6_partfun1(A_53)))), inference(resolution, [status(thm)], [c_40, c_124])).
% 4.88/1.97  tff(c_6, plain, (![A_3]: (k2_relat_1(A_3)!=k1_xboole_0 | k1_xboole_0=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.88/1.97  tff(c_159, plain, (![A_53]: (k2_relat_1(k6_partfun1(A_53))!=k1_xboole_0 | k6_partfun1(A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_6])).
% 4.88/1.97  tff(c_181, plain, (![A_58]: (k1_xboole_0!=A_58 | k6_partfun1(A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_159])).
% 4.88/1.97  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_192, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_181, c_54])).
% 4.88/1.97  tff(c_246, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_192])).
% 4.88/1.97  tff(c_70, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_68, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_135, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_124])).
% 4.88/1.97  tff(c_164, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.88/1.97  tff(c_175, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_164])).
% 4.88/1.97  tff(c_311, plain, (![B_76, A_77]: (k2_relat_1(B_76)=A_77 | ~v2_funct_2(B_76, A_77) | ~v5_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.88/1.97  tff(c_323, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_175, c_311])).
% 4.88/1.97  tff(c_335, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_323])).
% 4.88/1.97  tff(c_654, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_335])).
% 4.88/1.97  tff(c_66, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_795, plain, (![C_117, B_118, A_119]: (v2_funct_2(C_117, B_118) | ~v3_funct_2(C_117, A_119, B_118) | ~v1_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.88/1.97  tff(c_801, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_795])).
% 4.88/1.97  tff(c_809, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_801])).
% 4.88/1.97  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_654, c_809])).
% 4.88/1.97  tff(c_812, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_335])).
% 4.88/1.97  tff(c_825, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.88/1.97  tff(c_831, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_825])).
% 4.88/1.97  tff(c_838, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_812, c_831])).
% 4.88/1.97  tff(c_935, plain, (![C_128, A_129, B_130]: (v2_funct_1(C_128) | ~v3_funct_2(C_128, A_129, B_130) | ~v1_funct_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.88/1.97  tff(c_941, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_935])).
% 4.88/1.97  tff(c_948, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_941])).
% 4.88/1.97  tff(c_1440, plain, (![C_164, D_165, B_166, A_167]: (k2_funct_1(C_164)=D_165 | k1_xboole_0=B_166 | k1_xboole_0=A_167 | ~v2_funct_1(C_164) | ~r2_relset_1(A_167, A_167, k1_partfun1(A_167, B_166, B_166, A_167, C_164, D_165), k6_partfun1(A_167)) | k2_relset_1(A_167, B_166, C_164)!=B_166 | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(B_166, A_167))) | ~v1_funct_2(D_165, B_166, A_167) | ~v1_funct_1(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))) | ~v1_funct_2(C_164, A_167, B_166) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.88/1.97  tff(c_1452, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1440])).
% 4.88/1.97  tff(c_1455, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_56, c_838, c_948, c_1452])).
% 4.88/1.97  tff(c_1456, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_246, c_1455])).
% 4.88/1.97  tff(c_1134, plain, (![A_147, B_148]: (k2_funct_2(A_147, B_148)=k2_funct_1(B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(k2_zfmisc_1(A_147, A_147))) | ~v3_funct_2(B_148, A_147, A_147) | ~v1_funct_2(B_148, A_147, A_147) | ~v1_funct_1(B_148))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.88/1.97  tff(c_1140, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1134])).
% 4.88/1.97  tff(c_1148, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1140])).
% 4.88/1.97  tff(c_52, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_1152, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_52])).
% 4.88/1.97  tff(c_1457, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_1152])).
% 4.88/1.97  tff(c_1461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_304, c_1457])).
% 4.88/1.97  tff(c_1463, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_192])).
% 4.88/1.97  tff(c_144, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_135, c_6])).
% 4.88/1.97  tff(c_178, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_144])).
% 4.88/1.97  tff(c_1467, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1463, c_178])).
% 4.88/1.97  tff(c_1578, plain, (![B_180, A_181]: (k2_relat_1(B_180)=A_181 | ~v2_funct_2(B_180, A_181) | ~v5_relat_1(B_180, A_181) | ~v1_relat_1(B_180))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.88/1.97  tff(c_1590, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_175, c_1578])).
% 4.88/1.97  tff(c_1603, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_1590])).
% 4.88/1.97  tff(c_1604, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1467, c_1603])).
% 4.88/1.97  tff(c_1724, plain, (![C_195, B_196, A_197]: (v2_funct_2(C_195, B_196) | ~v3_funct_2(C_195, A_197, B_196) | ~v1_funct_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.88/1.97  tff(c_1730, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1724])).
% 4.88/1.97  tff(c_1738, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1730])).
% 4.88/1.97  tff(c_1740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1604, c_1738])).
% 4.88/1.97  tff(c_1741, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_144])).
% 4.88/1.97  tff(c_163, plain, (![A_53]: (k1_xboole_0!=A_53 | k6_partfun1(A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_159])).
% 4.88/1.97  tff(c_1786, plain, (![A_203]: (A_203!='#skF_2' | k6_partfun1(A_203)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1741, c_163])).
% 4.88/1.97  tff(c_1800, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2') | '#skF_2'!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1786, c_54])).
% 4.88/1.97  tff(c_1857, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_1800])).
% 4.88/1.97  tff(c_1742, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_144])).
% 4.88/1.97  tff(c_1754, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1742])).
% 4.88/1.97  tff(c_1943, plain, (![B_215, A_216]: (k2_relat_1(B_215)=A_216 | ~v2_funct_2(B_215, A_216) | ~v5_relat_1(B_215, A_216) | ~v1_relat_1(B_215))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.88/1.97  tff(c_1955, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_175, c_1943])).
% 4.88/1.97  tff(c_1967, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_1754, c_1955])).
% 4.88/1.97  tff(c_1968, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1857, c_1967])).
% 4.88/1.97  tff(c_2083, plain, (![C_233, B_234, A_235]: (v2_funct_2(C_233, B_234) | ~v3_funct_2(C_233, A_235, B_234) | ~v1_funct_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_235, B_234))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.88/1.97  tff(c_2089, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2083])).
% 4.88/1.97  tff(c_2097, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2089])).
% 4.88/1.97  tff(c_2099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1968, c_2097])).
% 4.88/1.97  tff(c_2101, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1800])).
% 4.88/1.97  tff(c_136, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_124])).
% 4.88/1.97  tff(c_152, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_136, c_6])).
% 4.88/1.97  tff(c_1767, plain, (k2_relat_1('#skF_3')!='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1741, c_152])).
% 4.88/1.97  tff(c_1768, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_1767])).
% 4.88/1.97  tff(c_2108, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2101, c_1768])).
% 4.88/1.97  tff(c_176, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_164])).
% 4.88/1.97  tff(c_2133, plain, (![B_236, A_237]: (k2_relat_1(B_236)=A_237 | ~v2_funct_2(B_236, A_237) | ~v5_relat_1(B_236, A_237) | ~v1_relat_1(B_236))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.88/1.97  tff(c_2139, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_176, c_2133])).
% 4.88/1.97  tff(c_2145, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2139])).
% 4.88/1.97  tff(c_2298, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2108, c_2145])).
% 4.88/1.97  tff(c_58, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.88/1.97  tff(c_2404, plain, (![C_262, B_263, A_264]: (v2_funct_2(C_262, B_263) | ~v3_funct_2(C_262, A_264, B_263) | ~v1_funct_1(C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_264, B_263))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.88/1.97  tff(c_2413, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2404])).
% 4.88/1.97  tff(c_2421, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2413])).
% 4.88/1.97  tff(c_2423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2298, c_2421])).
% 4.88/1.97  tff(c_2424, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1767])).
% 4.88/1.97  tff(c_2430, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2424, c_1741])).
% 4.88/1.97  tff(c_10, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.88/1.97  tff(c_73, plain, (![A_4]: (k1_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 4.88/1.97  tff(c_8, plain, (![A_3]: (k1_relat_1(A_3)!=k1_xboole_0 | k1_xboole_0=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.88/1.97  tff(c_156, plain, (![A_53]: (k1_relat_1(k6_partfun1(A_53))!=k1_xboole_0 | k6_partfun1(A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_8])).
% 4.88/1.97  tff(c_161, plain, (![A_53]: (k1_xboole_0!=A_53 | k6_partfun1(A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_156])).
% 4.88/1.97  tff(c_2480, plain, (![A_270]: (A_270!='#skF_3' | k6_partfun1(A_270)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2430, c_2430, c_161])).
% 4.88/1.97  tff(c_2519, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2480, c_73])).
% 4.88/1.97  tff(c_151, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_136, c_8])).
% 4.88/1.97  tff(c_1759, plain, (k1_relat_1('#skF_3')!='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1741, c_151])).
% 4.88/1.97  tff(c_1760, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_1759])).
% 4.88/1.97  tff(c_2427, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2424, c_1760])).
% 4.88/1.97  tff(c_2522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2519, c_2427])).
% 4.88/1.97  tff(c_2523, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1759])).
% 4.88/1.97  tff(c_2527, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_1741])).
% 4.88/1.97  tff(c_2594, plain, (![A_53]: (A_53!='#skF_3' | k6_partfun1(A_53)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2527, c_2527, c_163])).
% 4.88/1.97  tff(c_2530, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_54])).
% 4.88/1.97  tff(c_2636, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), '#skF_3') | '#skF_3'!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2594, c_2530])).
% 4.88/1.97  tff(c_2663, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_2636])).
% 4.88/1.97  tff(c_2525, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_2523, c_1754])).
% 4.88/1.97  tff(c_2720, plain, (![B_287, A_288]: (k2_relat_1(B_287)=A_288 | ~v2_funct_2(B_287, A_288) | ~v5_relat_1(B_287, A_288) | ~v1_relat_1(B_287))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.88/1.97  tff(c_2729, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_176, c_2720])).
% 4.88/1.97  tff(c_2738, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2525, c_2729])).
% 4.88/1.97  tff(c_2739, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2663, c_2738])).
% 4.88/1.97  tff(c_2818, plain, (![C_302, B_303, A_304]: (v2_funct_2(C_302, B_303) | ~v3_funct_2(C_302, A_304, B_303) | ~v1_funct_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_304, B_303))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.88/1.97  tff(c_2824, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2818])).
% 4.88/1.97  tff(c_2829, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2824])).
% 4.88/1.97  tff(c_2831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2739, c_2829])).
% 4.88/1.97  tff(c_2833, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2636])).
% 4.88/1.97  tff(c_2596, plain, (![A_278]: (A_278!='#skF_3' | k6_partfun1(A_278)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2527, c_2527, c_163])).
% 4.88/1.97  tff(c_2613, plain, (![A_278]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_278, A_278))) | A_278!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2596, c_40])).
% 4.88/1.97  tff(c_3243, plain, (![A_341]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_341, A_341))) | A_341!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2833, c_2613])).
% 4.88/1.97  tff(c_24, plain, (![A_15, B_16, D_18]: (r2_relset_1(A_15, B_16, D_18, D_18) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.88/1.97  tff(c_3293, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3243, c_24])).
% 4.88/1.97  tff(c_2852, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_60])).
% 4.88/1.97  tff(c_2853, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_58])).
% 4.88/1.97  tff(c_2854, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_62])).
% 4.88/1.97  tff(c_14, plain, (![A_5]: (k2_funct_1(k6_relat_1(A_5))=k6_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.88/1.97  tff(c_71, plain, (![A_5]: (k2_funct_1(k6_partfun1(A_5))=k6_partfun1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_14])).
% 4.88/1.97  tff(c_2616, plain, (![A_278]: (k6_partfun1(A_278)=k2_funct_1('#skF_3') | A_278!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2596, c_71])).
% 4.88/1.97  tff(c_3024, plain, (![A_320]: (k6_partfun1(A_320)=k2_funct_1('#skF_1') | A_320!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2833, c_2616])).
% 4.88/1.97  tff(c_3104, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3024, c_72])).
% 4.88/1.97  tff(c_134, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_40, c_124])).
% 4.88/1.97  tff(c_3044, plain, (![A_320]: (v1_relat_1(k2_funct_1('#skF_1')) | A_320!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3024, c_134])).
% 4.88/1.97  tff(c_3068, plain, (![A_320]: (A_320!='#skF_1')), inference(splitLeft, [status(thm)], [c_3044])).
% 4.88/1.97  tff(c_2844, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2833, c_2525])).
% 4.88/1.97  tff(c_2851, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_56])).
% 4.88/1.97  tff(c_22, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.88/1.97  tff(c_2949, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_1')=k2_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2851, c_22])).
% 4.88/1.97  tff(c_2962, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2844, c_2949])).
% 4.88/1.97  tff(c_3089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3068, c_2962])).
% 4.88/1.97  tff(c_3090, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_3044])).
% 4.88/1.97  tff(c_2848, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2523])).
% 4.88/1.97  tff(c_1744, plain, (![A_3]: (k2_relat_1(A_3)!='#skF_2' | A_3='#skF_2' | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_1741, c_6])).
% 4.88/1.97  tff(c_3157, plain, (![A_334]: (k2_relat_1(A_334)!='#skF_1' | A_334='#skF_1' | ~v1_relat_1(A_334))), inference(demodulation, [status(thm), theory('equality')], [c_2848, c_2848, c_1744])).
% 4.88/1.97  tff(c_3160, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_3090, c_3157])).
% 4.88/1.97  tff(c_3169, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3104, c_3160])).
% 4.88/1.97  tff(c_3240, plain, (![A_278]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_278, A_278))) | A_278!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2833, c_2613])).
% 4.88/1.97  tff(c_3301, plain, (![A_344, B_345]: (k2_funct_2(A_344, B_345)=k2_funct_1(B_345) | ~m1_subset_1(B_345, k1_zfmisc_1(k2_zfmisc_1(A_344, A_344))) | ~v3_funct_2(B_345, A_344, A_344) | ~v1_funct_2(B_345, A_344, A_344) | ~v1_funct_1(B_345))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.88/1.97  tff(c_3304, plain, (![A_278]: (k2_funct_2(A_278, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_278, A_278) | ~v1_funct_2('#skF_1', A_278, A_278) | ~v1_funct_1('#skF_1') | A_278!='#skF_1')), inference(resolution, [status(thm)], [c_3240, c_3301])).
% 4.88/1.97  tff(c_3352, plain, (![A_354]: (k2_funct_2(A_354, '#skF_1')='#skF_1' | ~v3_funct_2('#skF_1', A_354, A_354) | ~v1_funct_2('#skF_1', A_354, A_354) | A_354!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2854, c_3169, c_3304])).
% 4.88/1.97  tff(c_3355, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2853, c_3352])).
% 4.88/1.97  tff(c_3358, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2852, c_3355])).
% 4.88/1.97  tff(c_2531, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_52])).
% 4.88/1.97  tff(c_2843, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2833, c_2531])).
% 4.88/1.97  tff(c_3359, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3358, c_2843])).
% 4.88/1.97  tff(c_3362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3293, c_3359])).
% 4.88/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.97  
% 4.88/1.97  Inference rules
% 4.88/1.97  ----------------------
% 4.88/1.97  #Ref     : 24
% 4.88/1.97  #Sup     : 684
% 4.88/1.97  #Fact    : 0
% 4.88/1.97  #Define  : 0
% 4.88/1.97  #Split   : 28
% 4.88/1.97  #Chain   : 0
% 4.88/1.97  #Close   : 0
% 4.88/1.97  
% 4.88/1.97  Ordering : KBO
% 4.88/1.97  
% 4.88/1.97  Simplification rules
% 4.88/1.97  ----------------------
% 4.88/1.97  #Subsume      : 193
% 4.88/1.97  #Demod        : 648
% 4.88/1.97  #Tautology    : 323
% 4.88/1.97  #SimpNegUnit  : 61
% 4.88/1.97  #BackRed      : 131
% 4.88/1.97  
% 4.88/1.97  #Partial instantiations: 0
% 4.88/1.97  #Strategies tried      : 1
% 4.88/1.97  
% 4.88/1.97  Timing (in seconds)
% 4.88/1.97  ----------------------
% 4.88/1.97  Preprocessing        : 0.37
% 4.88/1.97  Parsing              : 0.21
% 4.88/1.97  CNF conversion       : 0.02
% 4.88/1.97  Main loop            : 0.75
% 4.88/1.97  Inferencing          : 0.26
% 4.88/1.97  Reduction            : 0.27
% 4.88/1.97  Demodulation         : 0.19
% 4.88/1.97  BG Simplification    : 0.03
% 4.88/1.97  Subsumption          : 0.11
% 4.88/1.97  Abstraction          : 0.03
% 4.88/1.97  MUC search           : 0.00
% 4.88/1.97  Cooper               : 0.00
% 4.88/1.97  Total                : 1.17
% 4.88/1.97  Index Insertion      : 0.00
% 4.88/1.97  Index Deletion       : 0.00
% 4.88/1.98  Index Matching       : 0.00
% 4.88/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
