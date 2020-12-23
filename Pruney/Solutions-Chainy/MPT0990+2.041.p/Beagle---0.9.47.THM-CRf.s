%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:01 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 687 expanded)
%              Number of leaves         :   41 ( 263 expanded)
%              Depth                    :   18
%              Number of atoms          :  301 (3002 expanded)
%              Number of equality atoms :  111 (1121 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_44,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_93,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_93])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_105,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_93])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_119,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_131,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_119])).

tff(c_221,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_230,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_221])).

tff(c_239,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_131,c_230])).

tff(c_240,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_239])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_149,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_158,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_149])).

tff(c_162,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_158])).

tff(c_46,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_12,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_relat_1(k2_relat_1(A_6)) != k5_relat_1(B_8,A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_522,plain,(
    ! [A_125,B_126] :
      ( k2_funct_1(A_125) = B_126
      | k6_partfun1(k2_relat_1(A_125)) != k5_relat_1(B_126,A_125)
      | k2_relat_1(B_126) != k1_relat_1(A_125)
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_528,plain,(
    ! [B_126] :
      ( k2_funct_1('#skF_3') = B_126
      | k5_relat_1(B_126,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_126) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_522])).

tff(c_533,plain,(
    ! [B_127] :
      ( k2_funct_1('#skF_3') = B_127
      | k5_relat_1(B_127,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_127) != '#skF_1'
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_72,c_56,c_240,c_528])).

tff(c_542,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_533])).

tff(c_549,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_542])).

tff(c_550,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_549])).

tff(c_551,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_42,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_107,plain,(
    ! [A_53,B_54,D_55] :
      ( r2_relset_1(A_53,B_54,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_114,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_42,c_107])).

tff(c_160,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_149])).

tff(c_455,plain,(
    ! [C_121,D_119,A_120,E_124,F_122,B_123] :
      ( m1_subset_1(k1_partfun1(A_120,B_123,C_121,D_119,E_124,F_122),k1_zfmisc_1(k2_zfmisc_1(A_120,D_119)))
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_121,D_119)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_120,B_123)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_310,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( D_86 = C_87
      | ~ r2_relset_1(A_88,B_89,C_87,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_318,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_310])).

tff(c_333,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_318])).

tff(c_336,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_471,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_336])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_471])).

tff(c_513,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_930,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( k2_relset_1(A_159,B_160,C_161) = B_160
      | ~ r2_relset_1(B_160,B_160,k1_partfun1(B_160,A_159,A_159,B_160,D_162,C_161),k6_partfun1(B_160))
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(B_160,A_159)))
      | ~ v1_funct_2(D_162,B_160,A_159)
      | ~ v1_funct_1(D_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_2(C_161,A_159,B_160)
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_936,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_930])).

tff(c_940,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_114,c_160,c_936])).

tff(c_942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_940])).

tff(c_943,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_130,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_119])).

tff(c_227,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_221])).

tff(c_235,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_130,c_227])).

tff(c_236,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_235])).

tff(c_944,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_73,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_partfun1(k2_relat_1(A_6)) != k5_relat_1(B_8,A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_948,plain,(
    ! [B_8] :
      ( k2_funct_1('#skF_4') = B_8
      | k5_relat_1(B_8,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_8) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_73])).

tff(c_952,plain,(
    ! [B_8] :
      ( k2_funct_1('#skF_4') = B_8
      | k5_relat_1(B_8,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_8) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_236,c_948])).

tff(c_960,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_952])).

tff(c_6,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_975,plain,(
    ! [A_174,E_170,C_173,D_175,B_171,F_172] :
      ( k1_partfun1(A_174,B_171,C_173,D_175,E_170,F_172) = k5_relat_1(E_170,F_172)
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_173,D_175)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_174,B_171)))
      | ~ v1_funct_1(E_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_979,plain,(
    ! [A_174,B_171,E_170] :
      ( k1_partfun1(A_174,B_171,'#skF_2','#skF_1',E_170,'#skF_4') = k5_relat_1(E_170,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_174,B_171)))
      | ~ v1_funct_1(E_170) ) ),
    inference(resolution,[status(thm)],[c_62,c_975])).

tff(c_1088,plain,(
    ! [A_190,B_191,E_192] :
      ( k1_partfun1(A_190,B_191,'#skF_2','#skF_1',E_192,'#skF_4') = k5_relat_1(E_192,'#skF_4')
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(E_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_979])).

tff(c_1100,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1088])).

tff(c_1108,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_513,c_1100])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( v2_funct_1(A_1)
      | k2_relat_1(B_3) != k1_relat_1(A_1)
      | ~ v2_funct_1(k5_relat_1(B_3,A_1))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1115,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1108,c_2])).

tff(c_1121,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_105,c_72,c_76,c_162,c_236,c_1115])).

tff(c_1123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_960,c_1121])).

tff(c_1125,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_1126,plain,(
    ! [B_193] :
      ( k2_funct_1('#skF_4') = B_193
      | k5_relat_1(B_193,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_193) != '#skF_2'
      | ~ v1_funct_1(B_193)
      | ~ v1_relat_1(B_193) ) ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_1132,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_1126])).

tff(c_1139,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_162,c_1132])).

tff(c_1143,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_1159,plain,(
    ! [F_203,E_201,C_204,A_205,B_202,D_206] :
      ( k1_partfun1(A_205,B_202,C_204,D_206,E_201,F_203) = k5_relat_1(E_201,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_204,D_206)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_205,B_202)))
      | ~ v1_funct_1(E_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1163,plain,(
    ! [A_205,B_202,E_201] :
      ( k1_partfun1(A_205,B_202,'#skF_2','#skF_1',E_201,'#skF_4') = k5_relat_1(E_201,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_205,B_202)))
      | ~ v1_funct_1(E_201) ) ),
    inference(resolution,[status(thm)],[c_62,c_1159])).

tff(c_1277,plain,(
    ! [A_221,B_222,E_223] :
      ( k1_partfun1(A_221,B_222,'#skF_2','#skF_1',E_223,'#skF_4') = k5_relat_1(E_223,'#skF_4')
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_1(E_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1163])).

tff(c_1289,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1277])).

tff(c_1297,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_513,c_1289])).

tff(c_1299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1143,c_1297])).

tff(c_1300,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_10,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k2_funct_1(A_5)) = k6_relat_1(k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k2_funct_1(A_5)) = k6_partfun1(k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_1312,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_74])).

tff(c_1323,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_1125,c_236,c_1312])).

tff(c_1325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_943,c_1323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:38:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.67  
% 3.80/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.67  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.80/1.67  
% 3.80/1.67  %Foreground sorts:
% 3.80/1.67  
% 3.80/1.67  
% 3.80/1.67  %Background operators:
% 3.80/1.67  
% 3.80/1.67  
% 3.80/1.67  %Foreground operators:
% 3.80/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.80/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.80/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.80/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.80/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.80/1.67  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.80/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.67  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.80/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.80/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.80/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.67  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.67  
% 3.80/1.69  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.80/1.69  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.80/1.69  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.80/1.69  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.80/1.69  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.80/1.69  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.80/1.69  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 3.80/1.69  tff(f_125, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.80/1.69  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.80/1.69  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.80/1.69  tff(f_154, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 3.80/1.69  tff(f_44, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 3.80/1.69  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.80/1.69  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 3.80/1.69  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.80/1.69  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_93, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.80/1.69  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_93])).
% 3.80/1.69  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_105, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_93])).
% 3.80/1.69  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_119, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.80/1.69  tff(c_131, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_119])).
% 3.80/1.69  tff(c_221, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.80/1.69  tff(c_230, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_221])).
% 3.80/1.69  tff(c_239, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_131, c_230])).
% 3.80/1.69  tff(c_240, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_239])).
% 3.80/1.69  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_149, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.80/1.69  tff(c_158, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_149])).
% 3.80/1.69  tff(c_162, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_158])).
% 3.80/1.69  tff(c_46, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.80/1.69  tff(c_12, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k2_relat_1(A_6))!=k5_relat_1(B_8, A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.80/1.69  tff(c_522, plain, (![A_125, B_126]: (k2_funct_1(A_125)=B_126 | k6_partfun1(k2_relat_1(A_125))!=k5_relat_1(B_126, A_125) | k2_relat_1(B_126)!=k1_relat_1(A_125) | ~v2_funct_1(A_125) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 3.80/1.69  tff(c_528, plain, (![B_126]: (k2_funct_1('#skF_3')=B_126 | k5_relat_1(B_126, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_126)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_522])).
% 3.80/1.69  tff(c_533, plain, (![B_127]: (k2_funct_1('#skF_3')=B_127 | k5_relat_1(B_127, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_127)!='#skF_1' | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_72, c_56, c_240, c_528])).
% 3.80/1.69  tff(c_542, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_104, c_533])).
% 3.80/1.69  tff(c_549, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_542])).
% 3.80/1.69  tff(c_550, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_549])).
% 3.80/1.69  tff(c_551, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_550])).
% 3.80/1.69  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_42, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.80/1.69  tff(c_107, plain, (![A_53, B_54, D_55]: (r2_relset_1(A_53, B_54, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.80/1.69  tff(c_114, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_42, c_107])).
% 3.80/1.69  tff(c_160, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_149])).
% 3.80/1.69  tff(c_455, plain, (![C_121, D_119, A_120, E_124, F_122, B_123]: (m1_subset_1(k1_partfun1(A_120, B_123, C_121, D_119, E_124, F_122), k1_zfmisc_1(k2_zfmisc_1(A_120, D_119))) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_121, D_119))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_120, B_123))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.80/1.69  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_310, plain, (![D_86, C_87, A_88, B_89]: (D_86=C_87 | ~r2_relset_1(A_88, B_89, C_87, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.80/1.69  tff(c_318, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_310])).
% 3.80/1.69  tff(c_333, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_318])).
% 3.80/1.69  tff(c_336, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_333])).
% 3.80/1.69  tff(c_471, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_336])).
% 3.80/1.69  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_471])).
% 3.80/1.69  tff(c_513, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_333])).
% 3.80/1.69  tff(c_930, plain, (![A_159, B_160, C_161, D_162]: (k2_relset_1(A_159, B_160, C_161)=B_160 | ~r2_relset_1(B_160, B_160, k1_partfun1(B_160, A_159, A_159, B_160, D_162, C_161), k6_partfun1(B_160)) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(B_160, A_159))) | ~v1_funct_2(D_162, B_160, A_159) | ~v1_funct_1(D_162) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_2(C_161, A_159, B_160) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.80/1.69  tff(c_936, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_513, c_930])).
% 3.80/1.69  tff(c_940, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_114, c_160, c_936])).
% 3.80/1.69  tff(c_942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_940])).
% 3.80/1.69  tff(c_943, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_550])).
% 3.80/1.69  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.80/1.69  tff(c_130, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_119])).
% 3.80/1.69  tff(c_227, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_221])).
% 3.80/1.69  tff(c_235, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_130, c_227])).
% 3.80/1.69  tff(c_236, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_235])).
% 3.80/1.69  tff(c_944, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_550])).
% 3.80/1.69  tff(c_73, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_partfun1(k2_relat_1(A_6))!=k5_relat_1(B_8, A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 3.80/1.69  tff(c_948, plain, (![B_8]: (k2_funct_1('#skF_4')=B_8 | k5_relat_1(B_8, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_8)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_944, c_73])).
% 3.80/1.69  tff(c_952, plain, (![B_8]: (k2_funct_1('#skF_4')=B_8 | k5_relat_1(B_8, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_8)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_236, c_948])).
% 3.80/1.69  tff(c_960, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_952])).
% 3.80/1.69  tff(c_6, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.80/1.69  tff(c_76, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 3.80/1.69  tff(c_975, plain, (![A_174, E_170, C_173, D_175, B_171, F_172]: (k1_partfun1(A_174, B_171, C_173, D_175, E_170, F_172)=k5_relat_1(E_170, F_172) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_173, D_175))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_174, B_171))) | ~v1_funct_1(E_170))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.80/1.69  tff(c_979, plain, (![A_174, B_171, E_170]: (k1_partfun1(A_174, B_171, '#skF_2', '#skF_1', E_170, '#skF_4')=k5_relat_1(E_170, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_174, B_171))) | ~v1_funct_1(E_170))), inference(resolution, [status(thm)], [c_62, c_975])).
% 3.80/1.69  tff(c_1088, plain, (![A_190, B_191, E_192]: (k1_partfun1(A_190, B_191, '#skF_2', '#skF_1', E_192, '#skF_4')=k5_relat_1(E_192, '#skF_4') | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(E_192))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_979])).
% 3.80/1.69  tff(c_1100, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1088])).
% 3.80/1.69  tff(c_1108, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_513, c_1100])).
% 3.80/1.69  tff(c_2, plain, (![A_1, B_3]: (v2_funct_1(A_1) | k2_relat_1(B_3)!=k1_relat_1(A_1) | ~v2_funct_1(k5_relat_1(B_3, A_1)) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.80/1.69  tff(c_1115, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1108, c_2])).
% 3.80/1.69  tff(c_1121, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_105, c_72, c_76, c_162, c_236, c_1115])).
% 3.80/1.69  tff(c_1123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_960, c_1121])).
% 3.80/1.69  tff(c_1125, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_952])).
% 3.80/1.69  tff(c_1126, plain, (![B_193]: (k2_funct_1('#skF_4')=B_193 | k5_relat_1(B_193, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_193)!='#skF_2' | ~v1_funct_1(B_193) | ~v1_relat_1(B_193))), inference(splitRight, [status(thm)], [c_952])).
% 3.80/1.69  tff(c_1132, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_1126])).
% 3.80/1.69  tff(c_1139, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_162, c_1132])).
% 3.80/1.69  tff(c_1143, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1139])).
% 3.80/1.69  tff(c_1159, plain, (![F_203, E_201, C_204, A_205, B_202, D_206]: (k1_partfun1(A_205, B_202, C_204, D_206, E_201, F_203)=k5_relat_1(E_201, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_204, D_206))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_205, B_202))) | ~v1_funct_1(E_201))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.80/1.69  tff(c_1163, plain, (![A_205, B_202, E_201]: (k1_partfun1(A_205, B_202, '#skF_2', '#skF_1', E_201, '#skF_4')=k5_relat_1(E_201, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_205, B_202))) | ~v1_funct_1(E_201))), inference(resolution, [status(thm)], [c_62, c_1159])).
% 3.80/1.69  tff(c_1277, plain, (![A_221, B_222, E_223]: (k1_partfun1(A_221, B_222, '#skF_2', '#skF_1', E_223, '#skF_4')=k5_relat_1(E_223, '#skF_4') | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_funct_1(E_223))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1163])).
% 3.80/1.69  tff(c_1289, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1277])).
% 3.80/1.69  tff(c_1297, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_513, c_1289])).
% 3.80/1.69  tff(c_1299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1143, c_1297])).
% 3.80/1.69  tff(c_1300, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1139])).
% 3.80/1.69  tff(c_10, plain, (![A_5]: (k5_relat_1(A_5, k2_funct_1(A_5))=k6_relat_1(k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.80/1.69  tff(c_74, plain, (![A_5]: (k5_relat_1(A_5, k2_funct_1(A_5))=k6_partfun1(k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 3.80/1.69  tff(c_1312, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1300, c_74])).
% 3.80/1.69  tff(c_1323, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_1125, c_236, c_1312])).
% 3.80/1.69  tff(c_1325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_943, c_1323])).
% 3.80/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.69  
% 3.80/1.69  Inference rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Ref     : 0
% 3.80/1.69  #Sup     : 268
% 3.80/1.69  #Fact    : 0
% 3.80/1.69  #Define  : 0
% 3.80/1.69  #Split   : 14
% 3.80/1.69  #Chain   : 0
% 3.80/1.69  #Close   : 0
% 3.80/1.69  
% 3.80/1.69  Ordering : KBO
% 3.80/1.69  
% 3.80/1.69  Simplification rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Subsume      : 2
% 3.80/1.69  #Demod        : 208
% 3.80/1.69  #Tautology    : 66
% 3.80/1.69  #SimpNegUnit  : 17
% 3.80/1.69  #BackRed      : 8
% 3.80/1.69  
% 3.80/1.69  #Partial instantiations: 0
% 3.80/1.69  #Strategies tried      : 1
% 3.80/1.69  
% 3.80/1.69  Timing (in seconds)
% 3.80/1.69  ----------------------
% 3.80/1.69  Preprocessing        : 0.39
% 3.80/1.69  Parsing              : 0.21
% 3.80/1.69  CNF conversion       : 0.02
% 3.80/1.69  Main loop            : 0.52
% 3.80/1.69  Inferencing          : 0.19
% 3.80/1.69  Reduction            : 0.17
% 3.80/1.69  Demodulation         : 0.12
% 3.80/1.70  BG Simplification    : 0.03
% 3.80/1.70  Subsumption          : 0.09
% 3.80/1.70  Abstraction          : 0.03
% 3.80/1.70  MUC search           : 0.00
% 3.80/1.70  Cooper               : 0.00
% 3.80/1.70  Total                : 0.95
% 3.80/1.70  Index Insertion      : 0.00
% 3.80/1.70  Index Deletion       : 0.00
% 3.80/1.70  Index Matching       : 0.00
% 3.80/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
