%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:54 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :  221 (2460 expanded)
%              Number of leaves         :   47 ( 825 expanded)
%              Depth                    :   18
%              Number of atoms          :  428 (5678 expanded)
%              Number of equality atoms :  153 (2288 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_209,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_143,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_187,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_42,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_354,plain,(
    ! [A_81,B_82,D_83] :
      ( r2_relset_1(A_81,B_82,D_83,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_362,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_354])).

tff(c_54,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [A_2] : k2_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_2] : k2_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_14,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,(
    ! [A_4] : v1_relat_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14])).

tff(c_153,plain,(
    ! [A_59] :
      ( k2_relat_1(A_59) != k1_xboole_0
      | k1_xboole_0 = A_59
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159,plain,(
    ! [A_4] :
      ( k2_relat_1(k6_partfun1(A_4)) != k1_xboole_0
      | k6_partfun1(A_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_83,c_153])).

tff(c_165,plain,(
    ! [A_4] :
      ( k1_xboole_0 != A_4
      | k6_partfun1(A_4) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_159])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_230,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_64])).

tff(c_276,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_80,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_78,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_74,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_214,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_227,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_214])).

tff(c_310,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_322,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_310])).

tff(c_388,plain,(
    ! [B_87,A_88] :
      ( k2_relat_1(B_87) = A_88
      | ~ v2_funct_2(B_87,A_88)
      | ~ v5_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_397,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_322,c_388])).

tff(c_409,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_397])).

tff(c_413,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_76,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_761,plain,(
    ! [C_122,B_123,A_124] :
      ( v2_funct_2(C_122,B_123)
      | ~ v3_funct_2(C_122,A_124,B_123)
      | ~ v1_funct_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_773,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_761])).

tff(c_785,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_773])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_785])).

tff(c_788,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_1059,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1071,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1059])).

tff(c_1079,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_1071])).

tff(c_48,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_361,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_48,c_354])).

tff(c_1100,plain,(
    ! [C_149,A_150,B_151] :
      ( v2_funct_1(C_149)
      | ~ v3_funct_2(C_149,A_150,B_151)
      | ~ v1_funct_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1112,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1100])).

tff(c_1124,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_1112])).

tff(c_1544,plain,(
    ! [E_199,D_194,C_198,A_196,F_197,B_195] :
      ( m1_subset_1(k1_partfun1(A_196,B_195,C_198,D_194,E_199,F_197),k1_zfmisc_1(k2_zfmisc_1(A_196,D_194)))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(C_198,D_194)))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195)))
      | ~ v1_funct_1(E_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1185,plain,(
    ! [D_160,C_161,A_162,B_163] :
      ( D_160 = C_161
      | ~ r2_relset_1(A_162,B_163,C_161,D_160)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1199,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_1185])).

tff(c_1222,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1199])).

tff(c_1311,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1222])).

tff(c_1550,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1544,c_1311])).

tff(c_1586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_74,c_72,c_66,c_1550])).

tff(c_1587,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1222])).

tff(c_2369,plain,(
    ! [C_252,D_253,B_254,A_255] :
      ( k2_funct_1(C_252) = D_253
      | k1_xboole_0 = B_254
      | k1_xboole_0 = A_255
      | ~ v2_funct_1(C_252)
      | ~ r2_relset_1(A_255,A_255,k1_partfun1(A_255,B_254,B_254,A_255,C_252,D_253),k6_partfun1(A_255))
      | k2_relset_1(A_255,B_254,C_252) != B_254
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(B_254,A_255)))
      | ~ v1_funct_2(D_253,B_254,A_255)
      | ~ v1_funct_1(D_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_255,B_254)))
      | ~ v1_funct_2(C_252,A_255,B_254)
      | ~ v1_funct_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2384,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1587,c_2369])).

tff(c_2398,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_66,c_1079,c_361,c_1124,c_2384])).

tff(c_2399,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_2398])).

tff(c_1245,plain,(
    ! [A_165,B_166] :
      ( k2_funct_2(A_165,B_166) = k2_funct_1(B_166)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(k2_zfmisc_1(A_165,A_165)))
      | ~ v3_funct_2(B_166,A_165,A_165)
      | ~ v1_funct_2(B_166,A_165,A_165)
      | ~ v1_funct_1(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1257,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1245])).

tff(c_1269,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1257])).

tff(c_62,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_1306,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_62])).

tff(c_2400,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2399,c_1306])).

tff(c_2404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_2400])).

tff(c_2406,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_94,plain,(
    ! [A_56] : k6_relat_1(A_56) = k6_partfun1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_100,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_12])).

tff(c_6,plain,(
    ! [A_2] : k1_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_57] : k1_relat_1(k6_partfun1(A_57)) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_130,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_121])).

tff(c_2415,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2406,c_130])).

tff(c_226,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_214])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_238,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_2423,plain,
    ( k2_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2406,c_238])).

tff(c_2424,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2423])).

tff(c_2448,plain,(
    ! [C_256,B_257,A_258] :
      ( v5_relat_1(C_256,B_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_258,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2459,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2448])).

tff(c_2540,plain,(
    ! [B_269,A_270] :
      ( k2_relat_1(B_269) = A_270
      | ~ v2_funct_2(B_269,A_270)
      | ~ v5_relat_1(B_269,A_270)
      | ~ v1_relat_1(B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2552,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2459,c_2540])).

tff(c_2565,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_2552])).

tff(c_2566,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2424,c_2565])).

tff(c_68,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_2720,plain,(
    ! [C_283,B_284,A_285] :
      ( v2_funct_2(C_283,B_284)
      | ~ v3_funct_2(C_283,A_285,B_284)
      | ~ v1_funct_1(C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2729,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2720])).

tff(c_2741,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2729])).

tff(c_2743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2566,c_2741])).

tff(c_2744,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2423])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_237,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_226,c_4])).

tff(c_247,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_2409,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_247])).

tff(c_2793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2415,c_2744,c_2409])).

tff(c_2794,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_2796,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_2812,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2794,c_2796])).

tff(c_137,plain,(
    ! [A_58] : k2_relat_1(k6_partfun1(A_58)) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_146,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_137])).

tff(c_2801,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2794,c_2794,c_146])).

tff(c_2961,plain,(
    ! [C_297,B_298,A_299] :
      ( v5_relat_1(C_297,B_298)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_299,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2976,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2961])).

tff(c_3035,plain,(
    ! [B_305,A_306] :
      ( k2_relat_1(B_305) = A_306
      | ~ v2_funct_2(B_305,A_306)
      | ~ v5_relat_1(B_305,A_306)
      | ~ v1_relat_1(B_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3047,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2976,c_3035])).

tff(c_3059,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_2801,c_3047])).

tff(c_3060,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2812,c_3059])).

tff(c_3250,plain,(
    ! [C_325,B_326,A_327] :
      ( v2_funct_2(C_325,B_326)
      | ~ v3_funct_2(C_325,A_327,B_326)
      | ~ v1_funct_1(C_325)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3259,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3250])).

tff(c_3271,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_3259])).

tff(c_3273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3060,c_3271])).

tff(c_3275,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_210,plain,(
    ! [A_63] : m1_subset_1(k6_partfun1(A_63),k1_zfmisc_1(k2_zfmisc_1(A_63,A_63))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_213,plain,(
    ! [A_4] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_4,A_4)))
      | k1_xboole_0 != A_4 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_210])).

tff(c_3906,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_4,A_4)))
      | A_4 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3275,c_3275,c_213])).

tff(c_3937,plain,(
    ! [A_388,B_389,D_390] :
      ( r2_relset_1(A_388,B_389,D_390,D_390)
      | ~ m1_subset_1(D_390,k1_zfmisc_1(k2_zfmisc_1(A_388,B_389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3951,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3906,c_3937])).

tff(c_3291,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3275,c_2794])).

tff(c_3278,plain,(
    ! [A_4] :
      ( A_4 != '#skF_3'
      | k6_partfun1(A_4) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2794,c_2794,c_165])).

tff(c_3773,plain,(
    ! [A_4] :
      ( A_4 != '#skF_1'
      | k6_partfun1(A_4) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_3291,c_3278])).

tff(c_3302,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_72])).

tff(c_4026,plain,(
    ! [C_402,A_403,B_404] :
      ( v2_funct_1(C_402)
      | ~ v3_funct_2(C_402,A_403,B_404)
      | ~ v1_funct_1(C_402)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(A_403,B_404))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4029,plain,(
    ! [A_4] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_4,A_4)
      | ~ v1_funct_1('#skF_1')
      | A_4 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3906,c_4026])).

tff(c_4035,plain,(
    ! [A_4] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_4,A_4)
      | A_4 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3302,c_4029])).

tff(c_4095,plain,(
    ~ v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4035])).

tff(c_3301,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_68])).

tff(c_4097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4095,c_3301])).

tff(c_4098,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4035])).

tff(c_16,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,(
    ! [A_4] : v1_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16])).

tff(c_86,plain,(
    ! [A_2] : k1_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_10,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k6_relat_1(k2_relat_1(A_3))) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3307,plain,(
    ! [A_328] :
      ( k5_relat_1(A_328,k6_partfun1(k2_relat_1(A_328))) = A_328
      | ~ v1_relat_1(A_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_3316,plain,(
    ! [A_2] :
      ( k5_relat_1(k6_partfun1(A_2),k6_partfun1(A_2)) = k6_partfun1(A_2)
      | ~ v1_relat_1(k6_partfun1(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_3307])).

tff(c_3320,plain,(
    ! [A_2] : k5_relat_1(k6_partfun1(A_2),k6_partfun1(A_2)) = k6_partfun1(A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_3316])).

tff(c_18,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k1_relat_1(A_5)) != k5_relat_1(A_5,B_7)
      | k2_relat_1(A_5) != k1_relat_1(B_7)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4455,plain,(
    ! [A_462,B_463] :
      ( k2_funct_1(A_462) = B_463
      | k6_partfun1(k1_relat_1(A_462)) != k5_relat_1(A_462,B_463)
      | k2_relat_1(A_462) != k1_relat_1(B_463)
      | ~ v2_funct_1(A_462)
      | ~ v1_funct_1(B_463)
      | ~ v1_relat_1(B_463)
      | ~ v1_funct_1(A_462)
      | ~ v1_relat_1(A_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18])).

tff(c_4459,plain,(
    ! [A_2] :
      ( k2_funct_1(k6_partfun1(A_2)) = k6_partfun1(A_2)
      | k6_partfun1(k1_relat_1(k6_partfun1(A_2))) != k6_partfun1(A_2)
      | k2_relat_1(k6_partfun1(A_2)) != k1_relat_1(k6_partfun1(A_2))
      | ~ v2_funct_1(k6_partfun1(A_2))
      | ~ v1_funct_1(k6_partfun1(A_2))
      | ~ v1_relat_1(k6_partfun1(A_2))
      | ~ v1_funct_1(k6_partfun1(A_2))
      | ~ v1_relat_1(k6_partfun1(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3320,c_4455])).

tff(c_4479,plain,(
    ! [A_464] :
      ( k2_funct_1(k6_partfun1(A_464)) = k6_partfun1(A_464)
      | ~ v2_funct_1(k6_partfun1(A_464)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_82,c_83,c_82,c_86,c_85,c_86,c_4459])).

tff(c_4482,plain,(
    ! [A_4] :
      ( k2_funct_1(k6_partfun1(A_4)) = k6_partfun1(A_4)
      | ~ v2_funct_1('#skF_1')
      | A_4 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3773,c_4479])).

tff(c_4486,plain,(
    ! [A_465] :
      ( k2_funct_1(k6_partfun1(A_465)) = k6_partfun1(A_465)
      | A_465 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4098,c_4482])).

tff(c_4499,plain,(
    ! [A_466] :
      ( k6_partfun1(A_466) = k2_funct_1('#skF_1')
      | A_466 != '#skF_1'
      | A_466 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3773,c_4486])).

tff(c_4573,plain,(
    ! [A_466] :
      ( v1_relat_1(k2_funct_1('#skF_1'))
      | A_466 != '#skF_1'
      | A_466 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_83])).

tff(c_4595,plain,(
    ! [A_466] :
      ( A_466 != '#skF_1'
      | A_466 != '#skF_1' ) ),
    inference(splitLeft,[status(thm)],[c_4573])).

tff(c_4601,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4595])).

tff(c_4602,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4573])).

tff(c_3277,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != '#skF_3'
      | A_1 = '#skF_3'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2794,c_2794,c_4])).

tff(c_3851,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != '#skF_1'
      | A_1 = '#skF_1'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_3291,c_3277])).

tff(c_4614,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4602,c_3851])).

tff(c_4670,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4614])).

tff(c_4568,plain,(
    ! [A_466] :
      ( k1_relat_1(k2_funct_1('#skF_1')) = A_466
      | A_466 != '#skF_1'
      | A_466 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_86])).

tff(c_4687,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4568])).

tff(c_4691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4670,c_4687])).

tff(c_4692,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4614])).

tff(c_3300,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_70])).

tff(c_4403,plain,(
    ! [A_448,B_449] :
      ( k2_funct_2(A_448,B_449) = k2_funct_1(B_449)
      | ~ m1_subset_1(B_449,k1_zfmisc_1(k2_zfmisc_1(A_448,A_448)))
      | ~ v3_funct_2(B_449,A_448,A_448)
      | ~ v1_funct_2(B_449,A_448,A_448)
      | ~ v1_funct_1(B_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4406,plain,(
    ! [A_4] :
      ( k2_funct_2(A_4,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_4,A_4)
      | ~ v1_funct_2('#skF_1',A_4,A_4)
      | ~ v1_funct_1('#skF_1')
      | A_4 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3906,c_4403])).

tff(c_4428,plain,(
    ! [A_456] :
      ( k2_funct_2(A_456,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_456,A_456)
      | ~ v1_funct_2('#skF_1',A_456,A_456)
      | A_456 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3302,c_4406])).

tff(c_4431,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3301,c_4428])).

tff(c_4434,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_4431])).

tff(c_246,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_3391,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3275,c_3275,c_246])).

tff(c_3392,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3391])).

tff(c_3362,plain,(
    ! [C_329,B_330,A_331] :
      ( v5_relat_1(C_329,B_330)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_331,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3370,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_3362])).

tff(c_3611,plain,(
    ! [B_355,A_356] :
      ( k2_relat_1(B_355) = A_356
      | ~ v2_funct_2(B_355,A_356)
      | ~ v5_relat_1(B_355,A_356)
      | ~ v1_relat_1(B_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3620,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3370,c_3611])).

tff(c_3629,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_3620])).

tff(c_3630,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3392,c_3629])).

tff(c_3731,plain,(
    ! [C_369,B_370,A_371] :
      ( v2_funct_2(C_369,B_370)
      | ~ v3_funct_2(C_369,A_371,B_370)
      | ~ v1_funct_1(C_369)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_371,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3740,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_3731])).

tff(c_3749,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3740])).

tff(c_3751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3630,c_3749])).

tff(c_3752,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3391])).

tff(c_3298,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_62])).

tff(c_3831,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3752,c_3298])).

tff(c_4435,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4434,c_3831])).

tff(c_4697,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4692,c_4435])).

tff(c_4704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3951,c_4697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.30/2.53  
% 7.30/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.30/2.53  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.30/2.53  
% 7.30/2.53  %Foreground sorts:
% 7.30/2.53  
% 7.30/2.53  
% 7.30/2.53  %Background operators:
% 7.30/2.53  
% 7.30/2.53  
% 7.30/2.53  %Foreground operators:
% 7.30/2.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.30/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.30/2.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.30/2.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.30/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.30/2.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.30/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.30/2.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.30/2.53  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.30/2.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.30/2.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.30/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.30/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.30/2.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.30/2.53  tff('#skF_3', type, '#skF_3': $i).
% 7.30/2.53  tff('#skF_1', type, '#skF_1': $i).
% 7.30/2.53  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.30/2.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.30/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.30/2.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.30/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.30/2.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.30/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.30/2.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.30/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.30/2.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.30/2.53  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.30/2.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.30/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.30/2.53  
% 7.30/2.56  tff(f_209, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 7.30/2.56  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.30/2.56  tff(f_143, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.30/2.56  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.30/2.56  tff(f_46, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.30/2.56  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.30/2.56  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.30/2.56  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.30/2.56  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.30/2.56  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.30/2.56  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.30/2.56  tff(f_121, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.30/2.56  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.30/2.56  tff(f_187, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.30/2.56  tff(f_141, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.30/2.56  tff(f_42, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.30/2.56  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.30/2.56  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 7.30/2.56  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_354, plain, (![A_81, B_82, D_83]: (r2_relset_1(A_81, B_82, D_83, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.30/2.56  tff(c_362, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_354])).
% 7.30/2.56  tff(c_54, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.30/2.56  tff(c_8, plain, (![A_2]: (k2_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.30/2.56  tff(c_85, plain, (![A_2]: (k2_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 7.30/2.56  tff(c_14, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.30/2.56  tff(c_83, plain, (![A_4]: (v1_relat_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14])).
% 7.30/2.56  tff(c_153, plain, (![A_59]: (k2_relat_1(A_59)!=k1_xboole_0 | k1_xboole_0=A_59 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.30/2.56  tff(c_159, plain, (![A_4]: (k2_relat_1(k6_partfun1(A_4))!=k1_xboole_0 | k6_partfun1(A_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_153])).
% 7.30/2.56  tff(c_165, plain, (![A_4]: (k1_xboole_0!=A_4 | k6_partfun1(A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_159])).
% 7.30/2.56  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_230, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_165, c_64])).
% 7.30/2.56  tff(c_276, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_230])).
% 7.30/2.56  tff(c_80, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_78, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_74, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_214, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.30/2.56  tff(c_227, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_214])).
% 7.30/2.56  tff(c_310, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.30/2.56  tff(c_322, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_310])).
% 7.30/2.56  tff(c_388, plain, (![B_87, A_88]: (k2_relat_1(B_87)=A_88 | ~v2_funct_2(B_87, A_88) | ~v5_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.30/2.56  tff(c_397, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_322, c_388])).
% 7.30/2.56  tff(c_409, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_397])).
% 7.30/2.56  tff(c_413, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_409])).
% 7.30/2.56  tff(c_76, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_761, plain, (![C_122, B_123, A_124]: (v2_funct_2(C_122, B_123) | ~v3_funct_2(C_122, A_124, B_123) | ~v1_funct_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.30/2.56  tff(c_773, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_761])).
% 7.30/2.56  tff(c_785, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_773])).
% 7.30/2.56  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_413, c_785])).
% 7.30/2.56  tff(c_788, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_409])).
% 7.30/2.56  tff(c_1059, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.30/2.56  tff(c_1071, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1059])).
% 7.30/2.56  tff(c_1079, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_788, c_1071])).
% 7.30/2.56  tff(c_48, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.30/2.56  tff(c_361, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_48, c_354])).
% 7.30/2.56  tff(c_1100, plain, (![C_149, A_150, B_151]: (v2_funct_1(C_149) | ~v3_funct_2(C_149, A_150, B_151) | ~v1_funct_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.30/2.56  tff(c_1112, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1100])).
% 7.30/2.56  tff(c_1124, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_1112])).
% 7.30/2.56  tff(c_1544, plain, (![E_199, D_194, C_198, A_196, F_197, B_195]: (m1_subset_1(k1_partfun1(A_196, B_195, C_198, D_194, E_199, F_197), k1_zfmisc_1(k2_zfmisc_1(A_196, D_194))) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(C_198, D_194))) | ~v1_funct_1(F_197) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))) | ~v1_funct_1(E_199))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.30/2.56  tff(c_1185, plain, (![D_160, C_161, A_162, B_163]: (D_160=C_161 | ~r2_relset_1(A_162, B_163, C_161, D_160) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.30/2.56  tff(c_1199, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_1185])).
% 7.30/2.56  tff(c_1222, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1199])).
% 7.30/2.56  tff(c_1311, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1222])).
% 7.30/2.56  tff(c_1550, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1544, c_1311])).
% 7.30/2.56  tff(c_1586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_74, c_72, c_66, c_1550])).
% 7.30/2.56  tff(c_1587, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1222])).
% 7.30/2.56  tff(c_2369, plain, (![C_252, D_253, B_254, A_255]: (k2_funct_1(C_252)=D_253 | k1_xboole_0=B_254 | k1_xboole_0=A_255 | ~v2_funct_1(C_252) | ~r2_relset_1(A_255, A_255, k1_partfun1(A_255, B_254, B_254, A_255, C_252, D_253), k6_partfun1(A_255)) | k2_relset_1(A_255, B_254, C_252)!=B_254 | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(B_254, A_255))) | ~v1_funct_2(D_253, B_254, A_255) | ~v1_funct_1(D_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_255, B_254))) | ~v1_funct_2(C_252, A_255, B_254) | ~v1_funct_1(C_252))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.30/2.56  tff(c_2384, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1587, c_2369])).
% 7.30/2.56  tff(c_2398, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_66, c_1079, c_361, c_1124, c_2384])).
% 7.30/2.56  tff(c_2399, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_276, c_2398])).
% 7.30/2.56  tff(c_1245, plain, (![A_165, B_166]: (k2_funct_2(A_165, B_166)=k2_funct_1(B_166) | ~m1_subset_1(B_166, k1_zfmisc_1(k2_zfmisc_1(A_165, A_165))) | ~v3_funct_2(B_166, A_165, A_165) | ~v1_funct_2(B_166, A_165, A_165) | ~v1_funct_1(B_166))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.30/2.56  tff(c_1257, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_1245])).
% 7.30/2.56  tff(c_1269, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1257])).
% 7.30/2.56  tff(c_62, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_1306, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1269, c_62])).
% 7.30/2.56  tff(c_2400, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2399, c_1306])).
% 7.30/2.56  tff(c_2404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_362, c_2400])).
% 7.30/2.56  tff(c_2406, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_230])).
% 7.30/2.56  tff(c_94, plain, (![A_56]: (k6_relat_1(A_56)=k6_partfun1(A_56))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.30/2.56  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.30/2.56  tff(c_100, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_12])).
% 7.30/2.56  tff(c_6, plain, (![A_2]: (k1_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.30/2.56  tff(c_121, plain, (![A_57]: (k1_relat_1(k6_partfun1(A_57))=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6])).
% 7.30/2.56  tff(c_130, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_121])).
% 7.30/2.56  tff(c_2415, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2406, c_130])).
% 7.30/2.56  tff(c_226, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_214])).
% 7.30/2.56  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.30/2.56  tff(c_238, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_226, c_2])).
% 7.30/2.56  tff(c_2423, plain, (k2_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2406, c_238])).
% 7.30/2.56  tff(c_2424, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2423])).
% 7.30/2.56  tff(c_2448, plain, (![C_256, B_257, A_258]: (v5_relat_1(C_256, B_257) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_258, B_257))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.30/2.56  tff(c_2459, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_2448])).
% 7.30/2.56  tff(c_2540, plain, (![B_269, A_270]: (k2_relat_1(B_269)=A_270 | ~v2_funct_2(B_269, A_270) | ~v5_relat_1(B_269, A_270) | ~v1_relat_1(B_269))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.30/2.56  tff(c_2552, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2459, c_2540])).
% 7.30/2.56  tff(c_2565, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_2552])).
% 7.30/2.56  tff(c_2566, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2424, c_2565])).
% 7.30/2.56  tff(c_68, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.30/2.56  tff(c_2720, plain, (![C_283, B_284, A_285]: (v2_funct_2(C_283, B_284) | ~v3_funct_2(C_283, A_285, B_284) | ~v1_funct_1(C_283) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.30/2.56  tff(c_2729, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2720])).
% 7.30/2.56  tff(c_2741, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2729])).
% 7.30/2.56  tff(c_2743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2566, c_2741])).
% 7.30/2.56  tff(c_2744, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2423])).
% 7.30/2.56  tff(c_4, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.30/2.56  tff(c_237, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_226, c_4])).
% 7.30/2.56  tff(c_247, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_237])).
% 7.30/2.56  tff(c_2409, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_247])).
% 7.30/2.56  tff(c_2793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2415, c_2744, c_2409])).
% 7.30/2.56  tff(c_2794, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_237])).
% 7.30/2.56  tff(c_2796, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_230])).
% 7.30/2.56  tff(c_2812, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2794, c_2796])).
% 7.30/2.56  tff(c_137, plain, (![A_58]: (k2_relat_1(k6_partfun1(A_58))=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 7.30/2.56  tff(c_146, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_137])).
% 7.30/2.56  tff(c_2801, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2794, c_2794, c_146])).
% 7.30/2.56  tff(c_2961, plain, (![C_297, B_298, A_299]: (v5_relat_1(C_297, B_298) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_299, B_298))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.30/2.56  tff(c_2976, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_2961])).
% 7.30/2.56  tff(c_3035, plain, (![B_305, A_306]: (k2_relat_1(B_305)=A_306 | ~v2_funct_2(B_305, A_306) | ~v5_relat_1(B_305, A_306) | ~v1_relat_1(B_305))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.30/2.56  tff(c_3047, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2976, c_3035])).
% 7.30/2.56  tff(c_3059, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_2801, c_3047])).
% 7.30/2.56  tff(c_3060, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2812, c_3059])).
% 7.30/2.56  tff(c_3250, plain, (![C_325, B_326, A_327]: (v2_funct_2(C_325, B_326) | ~v3_funct_2(C_325, A_327, B_326) | ~v1_funct_1(C_325) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.30/2.56  tff(c_3259, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3250])).
% 7.30/2.56  tff(c_3271, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_3259])).
% 7.30/2.56  tff(c_3273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3060, c_3271])).
% 7.30/2.56  tff(c_3275, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_230])).
% 7.30/2.56  tff(c_210, plain, (![A_63]: (m1_subset_1(k6_partfun1(A_63), k1_zfmisc_1(k2_zfmisc_1(A_63, A_63))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.30/2.56  tff(c_213, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_4, A_4))) | k1_xboole_0!=A_4)), inference(superposition, [status(thm), theory('equality')], [c_165, c_210])).
% 7.30/2.56  tff(c_3906, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_4, A_4))) | A_4!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3275, c_3275, c_213])).
% 7.30/2.56  tff(c_3937, plain, (![A_388, B_389, D_390]: (r2_relset_1(A_388, B_389, D_390, D_390) | ~m1_subset_1(D_390, k1_zfmisc_1(k2_zfmisc_1(A_388, B_389))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.30/2.56  tff(c_3951, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3906, c_3937])).
% 7.30/2.56  tff(c_3291, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3275, c_2794])).
% 7.30/2.56  tff(c_3278, plain, (![A_4]: (A_4!='#skF_3' | k6_partfun1(A_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2794, c_2794, c_165])).
% 7.30/2.56  tff(c_3773, plain, (![A_4]: (A_4!='#skF_1' | k6_partfun1(A_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_3291, c_3278])).
% 7.30/2.56  tff(c_3302, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_72])).
% 7.30/2.56  tff(c_4026, plain, (![C_402, A_403, B_404]: (v2_funct_1(C_402) | ~v3_funct_2(C_402, A_403, B_404) | ~v1_funct_1(C_402) | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(A_403, B_404))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.30/2.56  tff(c_4029, plain, (![A_4]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_4, A_4) | ~v1_funct_1('#skF_1') | A_4!='#skF_1')), inference(resolution, [status(thm)], [c_3906, c_4026])).
% 7.30/2.56  tff(c_4035, plain, (![A_4]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_4, A_4) | A_4!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3302, c_4029])).
% 7.30/2.56  tff(c_4095, plain, (~v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_4035])).
% 7.30/2.56  tff(c_3301, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_68])).
% 7.30/2.56  tff(c_4097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4095, c_3301])).
% 7.30/2.56  tff(c_4098, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_4035])).
% 7.30/2.56  tff(c_16, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.30/2.56  tff(c_82, plain, (![A_4]: (v1_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16])).
% 7.30/2.56  tff(c_86, plain, (![A_2]: (k1_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6])).
% 7.30/2.56  tff(c_10, plain, (![A_3]: (k5_relat_1(A_3, k6_relat_1(k2_relat_1(A_3)))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.30/2.56  tff(c_3307, plain, (![A_328]: (k5_relat_1(A_328, k6_partfun1(k2_relat_1(A_328)))=A_328 | ~v1_relat_1(A_328))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_10])).
% 7.30/2.56  tff(c_3316, plain, (![A_2]: (k5_relat_1(k6_partfun1(A_2), k6_partfun1(A_2))=k6_partfun1(A_2) | ~v1_relat_1(k6_partfun1(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_3307])).
% 7.30/2.56  tff(c_3320, plain, (![A_2]: (k5_relat_1(k6_partfun1(A_2), k6_partfun1(A_2))=k6_partfun1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_3316])).
% 7.30/2.56  tff(c_18, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k1_relat_1(A_5))!=k5_relat_1(A_5, B_7) | k2_relat_1(A_5)!=k1_relat_1(B_7) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.30/2.56  tff(c_4455, plain, (![A_462, B_463]: (k2_funct_1(A_462)=B_463 | k6_partfun1(k1_relat_1(A_462))!=k5_relat_1(A_462, B_463) | k2_relat_1(A_462)!=k1_relat_1(B_463) | ~v2_funct_1(A_462) | ~v1_funct_1(B_463) | ~v1_relat_1(B_463) | ~v1_funct_1(A_462) | ~v1_relat_1(A_462))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18])).
% 7.30/2.56  tff(c_4459, plain, (![A_2]: (k2_funct_1(k6_partfun1(A_2))=k6_partfun1(A_2) | k6_partfun1(k1_relat_1(k6_partfun1(A_2)))!=k6_partfun1(A_2) | k2_relat_1(k6_partfun1(A_2))!=k1_relat_1(k6_partfun1(A_2)) | ~v2_funct_1(k6_partfun1(A_2)) | ~v1_funct_1(k6_partfun1(A_2)) | ~v1_relat_1(k6_partfun1(A_2)) | ~v1_funct_1(k6_partfun1(A_2)) | ~v1_relat_1(k6_partfun1(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_3320, c_4455])).
% 7.30/2.56  tff(c_4479, plain, (![A_464]: (k2_funct_1(k6_partfun1(A_464))=k6_partfun1(A_464) | ~v2_funct_1(k6_partfun1(A_464)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_82, c_83, c_82, c_86, c_85, c_86, c_4459])).
% 7.30/2.56  tff(c_4482, plain, (![A_4]: (k2_funct_1(k6_partfun1(A_4))=k6_partfun1(A_4) | ~v2_funct_1('#skF_1') | A_4!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3773, c_4479])).
% 7.30/2.56  tff(c_4486, plain, (![A_465]: (k2_funct_1(k6_partfun1(A_465))=k6_partfun1(A_465) | A_465!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4098, c_4482])).
% 7.30/2.56  tff(c_4499, plain, (![A_466]: (k6_partfun1(A_466)=k2_funct_1('#skF_1') | A_466!='#skF_1' | A_466!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3773, c_4486])).
% 7.30/2.56  tff(c_4573, plain, (![A_466]: (v1_relat_1(k2_funct_1('#skF_1')) | A_466!='#skF_1' | A_466!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4499, c_83])).
% 7.30/2.56  tff(c_4595, plain, (![A_466]: (A_466!='#skF_1' | A_466!='#skF_1')), inference(splitLeft, [status(thm)], [c_4573])).
% 7.30/2.56  tff(c_4601, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_4595])).
% 7.30/2.56  tff(c_4602, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4573])).
% 7.30/2.56  tff(c_3277, plain, (![A_1]: (k1_relat_1(A_1)!='#skF_3' | A_1='#skF_3' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2794, c_2794, c_4])).
% 7.30/2.56  tff(c_3851, plain, (![A_1]: (k1_relat_1(A_1)!='#skF_1' | A_1='#skF_1' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_3291, c_3277])).
% 7.30/2.56  tff(c_4614, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4602, c_3851])).
% 7.30/2.56  tff(c_4670, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_4614])).
% 7.30/2.56  tff(c_4568, plain, (![A_466]: (k1_relat_1(k2_funct_1('#skF_1'))=A_466 | A_466!='#skF_1' | A_466!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4499, c_86])).
% 7.30/2.56  tff(c_4687, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_4568])).
% 7.30/2.56  tff(c_4691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4670, c_4687])).
% 7.30/2.56  tff(c_4692, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_4614])).
% 7.30/2.56  tff(c_3300, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_70])).
% 7.30/2.56  tff(c_4403, plain, (![A_448, B_449]: (k2_funct_2(A_448, B_449)=k2_funct_1(B_449) | ~m1_subset_1(B_449, k1_zfmisc_1(k2_zfmisc_1(A_448, A_448))) | ~v3_funct_2(B_449, A_448, A_448) | ~v1_funct_2(B_449, A_448, A_448) | ~v1_funct_1(B_449))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.30/2.56  tff(c_4406, plain, (![A_4]: (k2_funct_2(A_4, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_4, A_4) | ~v1_funct_2('#skF_1', A_4, A_4) | ~v1_funct_1('#skF_1') | A_4!='#skF_1')), inference(resolution, [status(thm)], [c_3906, c_4403])).
% 7.30/2.56  tff(c_4428, plain, (![A_456]: (k2_funct_2(A_456, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_456, A_456) | ~v1_funct_2('#skF_1', A_456, A_456) | A_456!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3302, c_4406])).
% 7.30/2.56  tff(c_4431, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3301, c_4428])).
% 7.30/2.56  tff(c_4434, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3300, c_4431])).
% 7.30/2.56  tff(c_246, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_227, c_2])).
% 7.30/2.56  tff(c_3391, plain, (k2_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3275, c_3275, c_246])).
% 7.30/2.56  tff(c_3392, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3391])).
% 7.30/2.56  tff(c_3362, plain, (![C_329, B_330, A_331]: (v5_relat_1(C_329, B_330) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_331, B_330))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.30/2.56  tff(c_3370, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_3362])).
% 7.30/2.56  tff(c_3611, plain, (![B_355, A_356]: (k2_relat_1(B_355)=A_356 | ~v2_funct_2(B_355, A_356) | ~v5_relat_1(B_355, A_356) | ~v1_relat_1(B_355))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.30/2.56  tff(c_3620, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3370, c_3611])).
% 7.30/2.56  tff(c_3629, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_3620])).
% 7.30/2.56  tff(c_3630, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3392, c_3629])).
% 7.30/2.56  tff(c_3731, plain, (![C_369, B_370, A_371]: (v2_funct_2(C_369, B_370) | ~v3_funct_2(C_369, A_371, B_370) | ~v1_funct_1(C_369) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_371, B_370))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.30/2.56  tff(c_3740, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_3731])).
% 7.30/2.56  tff(c_3749, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3740])).
% 7.30/2.56  tff(c_3751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3630, c_3749])).
% 7.30/2.56  tff(c_3752, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3391])).
% 7.30/2.56  tff(c_3298, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_62])).
% 7.30/2.56  tff(c_3831, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3752, c_3298])).
% 7.30/2.56  tff(c_4435, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4434, c_3831])).
% 7.30/2.56  tff(c_4697, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4692, c_4435])).
% 7.30/2.56  tff(c_4704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3951, c_4697])).
% 7.30/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.30/2.56  
% 7.30/2.56  Inference rules
% 7.30/2.56  ----------------------
% 7.30/2.56  #Ref     : 5
% 7.30/2.56  #Sup     : 1022
% 7.30/2.56  #Fact    : 0
% 7.30/2.56  #Define  : 0
% 7.30/2.56  #Split   : 34
% 7.30/2.56  #Chain   : 0
% 7.30/2.56  #Close   : 0
% 7.30/2.56  
% 7.30/2.56  Ordering : KBO
% 7.30/2.56  
% 7.30/2.56  Simplification rules
% 7.30/2.56  ----------------------
% 7.30/2.56  #Subsume      : 107
% 7.30/2.56  #Demod        : 967
% 7.30/2.56  #Tautology    : 426
% 7.30/2.56  #SimpNegUnit  : 18
% 7.30/2.56  #BackRed      : 72
% 7.30/2.56  
% 7.30/2.56  #Partial instantiations: 0
% 7.30/2.56  #Strategies tried      : 1
% 7.30/2.56  
% 7.30/2.56  Timing (in seconds)
% 7.30/2.56  ----------------------
% 7.30/2.56  Preprocessing        : 0.62
% 7.30/2.56  Parsing              : 0.32
% 7.30/2.56  CNF conversion       : 0.05
% 7.30/2.56  Main loop            : 1.09
% 7.30/2.56  Inferencing          : 0.36
% 7.30/2.56  Reduction            : 0.41
% 7.30/2.56  Demodulation         : 0.30
% 7.30/2.56  BG Simplification    : 0.05
% 7.30/2.56  Subsumption          : 0.18
% 7.30/2.56  Abstraction          : 0.06
% 7.30/2.56  MUC search           : 0.00
% 7.30/2.56  Cooper               : 0.00
% 7.30/2.56  Total                : 1.77
% 7.30/2.56  Index Insertion      : 0.00
% 7.30/2.56  Index Deletion       : 0.00
% 7.30/2.56  Index Matching       : 0.00
% 7.30/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
