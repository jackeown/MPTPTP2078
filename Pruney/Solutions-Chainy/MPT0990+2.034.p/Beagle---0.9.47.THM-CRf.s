%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:00 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 758 expanded)
%              Number of leaves         :   41 ( 288 expanded)
%              Depth                    :   17
%              Number of atoms          :  326 (3362 expanded)
%              Number of equality atoms :  123 (1250 expanded)
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

tff(f_188,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_117,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_146,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_46,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_95,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_108,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_95])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_95])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_152,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_163,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_152])).

tff(c_205,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_211,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_205])).

tff(c_219,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_163,c_211])).

tff(c_220,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_219])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_121,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_relset_1(A_60,B_61,C_62) = k2_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_127,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_121])).

tff(c_133,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_127])).

tff(c_44,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_644,plain,(
    ! [A_143,B_144] :
      ( k2_funct_1(A_143) = B_144
      | k6_partfun1(k2_relat_1(A_143)) != k5_relat_1(B_144,A_143)
      | k2_relat_1(B_144) != k1_relat_1(A_143)
      | ~ v2_funct_1(A_143)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_646,plain,(
    ! [B_144] :
      ( k2_funct_1('#skF_3') = B_144
      | k5_relat_1(B_144,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_144) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_644])).

tff(c_649,plain,(
    ! [B_145] :
      ( k2_funct_1('#skF_3') = B_145
      | k5_relat_1(B_145,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_145) != '#skF_1'
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_74,c_58,c_220,c_646])).

tff(c_652,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_649])).

tff(c_661,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_652])).

tff(c_662,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_661])).

tff(c_667,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_40,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_109,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_116,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_40,c_109])).

tff(c_134,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_121])).

tff(c_374,plain,(
    ! [E_108,B_107,A_109,C_111,F_110,D_106] :
      ( k1_partfun1(A_109,B_107,C_111,D_106,E_108,F_110) = k5_relat_1(E_108,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_111,D_106)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_380,plain,(
    ! [A_109,B_107,E_108] :
      ( k1_partfun1(A_109,B_107,'#skF_2','#skF_1',E_108,'#skF_4') = k5_relat_1(E_108,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(resolution,[status(thm)],[c_64,c_374])).

tff(c_390,plain,(
    ! [A_114,B_115,E_116] :
      ( k1_partfun1(A_114,B_115,'#skF_2','#skF_1',E_116,'#skF_4') = k5_relat_1(E_116,'#skF_4')
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_1(E_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_380])).

tff(c_396,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_390])).

tff(c_403,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_396])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_275,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( D_86 = C_87
      | ~ r2_relset_1(A_88,B_89,C_87,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_283,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_275])).

tff(c_298,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_283])).

tff(c_299,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_408,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_299])).

tff(c_543,plain,(
    ! [C_137,A_141,D_142,B_138,F_140,E_139] :
      ( m1_subset_1(k1_partfun1(A_141,B_138,C_137,D_142,E_139,F_140),k1_zfmisc_1(k2_zfmisc_1(A_141,D_142)))
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_137,D_142)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_138)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_606,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_543])).

tff(c_632,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_606])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_632])).

tff(c_635,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_1225,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( k2_relset_1(A_187,B_188,C_189) = B_188
      | ~ r2_relset_1(B_188,B_188,k1_partfun1(B_188,A_187,A_187,B_188,D_190,C_189),k6_partfun1(B_188))
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(B_188,A_187)))
      | ~ v1_funct_2(D_190,B_188,A_187)
      | ~ v1_funct_1(D_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(C_189,A_187,B_188)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1231,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_1225])).

tff(c_1235,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_116,c_134,c_1231])).

tff(c_1237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_1235])).

tff(c_1238,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_1239,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_1240,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1239,c_134])).

tff(c_164,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_205])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_164,c_214])).

tff(c_224,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_223])).

tff(c_75,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_partfun1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_1243,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_75])).

tff(c_1247,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_68,c_224,c_1243])).

tff(c_1255,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1247])).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_1270,plain,(
    ! [C_203,B_199,F_202,E_200,D_198,A_201] :
      ( k1_partfun1(A_201,B_199,C_203,D_198,E_200,F_202) = k5_relat_1(E_200,F_202)
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(C_203,D_198)))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_199)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1276,plain,(
    ! [A_201,B_199,E_200] :
      ( k1_partfun1(A_201,B_199,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_199)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_64,c_1270])).

tff(c_1358,plain,(
    ! [A_215,B_216,E_217] :
      ( k1_partfun1(A_215,B_216,'#skF_2','#skF_1',E_217,'#skF_4') = k5_relat_1(E_217,'#skF_4')
      | ~ m1_subset_1(E_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_1(E_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1276])).

tff(c_1364,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1358])).

tff(c_1371,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_635,c_1364])).

tff(c_6,plain,(
    ! [A_2,B_4] :
      ( v2_funct_1(A_2)
      | k2_relat_1(B_4) != k1_relat_1(A_2)
      | ~ v2_funct_1(k5_relat_1(B_4,A_2))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1381,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_6])).

tff(c_1387,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_68,c_107,c_74,c_76,c_133,c_224,c_1381])).

tff(c_1389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1255,c_1387])).

tff(c_1391,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1247])).

tff(c_1392,plain,(
    ! [B_218] :
      ( k2_funct_1('#skF_4') = B_218
      | k5_relat_1(B_218,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_218) != '#skF_2'
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218) ) ),
    inference(splitRight,[status(thm)],[c_1247])).

tff(c_1398,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_1392])).

tff(c_1407,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_133,c_1398])).

tff(c_1409,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1407])).

tff(c_1464,plain,(
    ! [C_238,B_234,E_235,D_233,F_237,A_236] :
      ( k1_partfun1(A_236,B_234,C_238,D_233,E_235,F_237) = k5_relat_1(E_235,F_237)
      | ~ m1_subset_1(F_237,k1_zfmisc_1(k2_zfmisc_1(C_238,D_233)))
      | ~ v1_funct_1(F_237)
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1470,plain,(
    ! [A_236,B_234,E_235] :
      ( k1_partfun1(A_236,B_234,'#skF_2','#skF_1',E_235,'#skF_4') = k5_relat_1(E_235,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(resolution,[status(thm)],[c_64,c_1464])).

tff(c_1484,plain,(
    ! [A_240,B_241,E_242] :
      ( k1_partfun1(A_240,B_241,'#skF_2','#skF_1',E_242,'#skF_4') = k5_relat_1(E_242,'#skF_4')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1470])).

tff(c_1490,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1484])).

tff(c_1497,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_635,c_1490])).

tff(c_1499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1409,c_1497])).

tff(c_1500,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1407])).

tff(c_1646,plain,(
    ! [A_269,C_270,B_271] :
      ( k6_partfun1(A_269) = k5_relat_1(C_270,k2_funct_1(C_270))
      | k1_xboole_0 = B_271
      | ~ v2_funct_1(C_270)
      | k2_relset_1(A_269,B_271,C_270) != B_271
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_269,B_271)))
      | ~ v1_funct_2(C_270,A_269,B_271)
      | ~ v1_funct_1(C_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1652,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1646])).

tff(c_1662,plain,
    ( k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1240,c_1391,c_1500,c_1652])).

tff(c_1664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1238,c_1662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.75  
% 4.12/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.75  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.12/1.75  
% 4.12/1.75  %Foreground sorts:
% 4.12/1.75  
% 4.12/1.75  
% 4.12/1.75  %Background operators:
% 4.12/1.75  
% 4.12/1.75  
% 4.12/1.75  %Foreground operators:
% 4.12/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.12/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.75  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.12/1.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.12/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.12/1.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.12/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.12/1.75  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.12/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.12/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.12/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.12/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.75  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.12/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.12/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.75  
% 4.53/1.77  tff(f_188, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.53/1.77  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.53/1.77  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.53/1.77  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.53/1.77  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.53/1.77  tff(f_129, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.53/1.77  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.53/1.77  tff(f_117, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.53/1.77  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.53/1.77  tff(f_127, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.53/1.77  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.53/1.77  tff(f_146, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.53/1.77  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.53/1.77  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.53/1.77  tff(f_162, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 4.53/1.77  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_95, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.53/1.77  tff(c_108, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_95])).
% 4.53/1.77  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_95])).
% 4.53/1.77  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_152, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.53/1.77  tff(c_163, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_152])).
% 4.53/1.77  tff(c_205, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.53/1.77  tff(c_211, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_205])).
% 4.53/1.77  tff(c_219, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_163, c_211])).
% 4.53/1.77  tff(c_220, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_219])).
% 4.53/1.77  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_121, plain, (![A_60, B_61, C_62]: (k2_relset_1(A_60, B_61, C_62)=k2_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.53/1.77  tff(c_127, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_121])).
% 4.53/1.77  tff(c_133, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_127])).
% 4.53/1.77  tff(c_44, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.53/1.77  tff(c_10, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.53/1.77  tff(c_644, plain, (![A_143, B_144]: (k2_funct_1(A_143)=B_144 | k6_partfun1(k2_relat_1(A_143))!=k5_relat_1(B_144, A_143) | k2_relat_1(B_144)!=k1_relat_1(A_143) | ~v2_funct_1(A_143) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 4.53/1.77  tff(c_646, plain, (![B_144]: (k2_funct_1('#skF_3')=B_144 | k5_relat_1(B_144, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_144)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_644])).
% 4.53/1.77  tff(c_649, plain, (![B_145]: (k2_funct_1('#skF_3')=B_145 | k5_relat_1(B_145, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_145)!='#skF_1' | ~v1_funct_1(B_145) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_74, c_58, c_220, c_646])).
% 4.53/1.77  tff(c_652, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_108, c_649])).
% 4.53/1.77  tff(c_661, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_652])).
% 4.53/1.77  tff(c_662, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_661])).
% 4.53/1.77  tff(c_667, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_662])).
% 4.53/1.77  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_40, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.53/1.77  tff(c_109, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.53/1.77  tff(c_116, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_40, c_109])).
% 4.53/1.77  tff(c_134, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_121])).
% 4.53/1.77  tff(c_374, plain, (![E_108, B_107, A_109, C_111, F_110, D_106]: (k1_partfun1(A_109, B_107, C_111, D_106, E_108, F_110)=k5_relat_1(E_108, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_111, D_106))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_107))) | ~v1_funct_1(E_108))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.53/1.77  tff(c_380, plain, (![A_109, B_107, E_108]: (k1_partfun1(A_109, B_107, '#skF_2', '#skF_1', E_108, '#skF_4')=k5_relat_1(E_108, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_107))) | ~v1_funct_1(E_108))), inference(resolution, [status(thm)], [c_64, c_374])).
% 4.53/1.77  tff(c_390, plain, (![A_114, B_115, E_116]: (k1_partfun1(A_114, B_115, '#skF_2', '#skF_1', E_116, '#skF_4')=k5_relat_1(E_116, '#skF_4') | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_1(E_116))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_380])).
% 4.53/1.77  tff(c_396, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_390])).
% 4.53/1.77  tff(c_403, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_396])).
% 4.53/1.77  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.53/1.77  tff(c_275, plain, (![D_86, C_87, A_88, B_89]: (D_86=C_87 | ~r2_relset_1(A_88, B_89, C_87, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.53/1.77  tff(c_283, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_275])).
% 4.53/1.77  tff(c_298, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_283])).
% 4.53/1.77  tff(c_299, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_298])).
% 4.53/1.77  tff(c_408, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_299])).
% 4.53/1.77  tff(c_543, plain, (![C_137, A_141, D_142, B_138, F_140, E_139]: (m1_subset_1(k1_partfun1(A_141, B_138, C_137, D_142, E_139, F_140), k1_zfmisc_1(k2_zfmisc_1(A_141, D_142))) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_137, D_142))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_138))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.53/1.77  tff(c_606, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_403, c_543])).
% 4.53/1.77  tff(c_632, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_606])).
% 4.53/1.77  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_408, c_632])).
% 4.53/1.77  tff(c_635, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_298])).
% 4.53/1.77  tff(c_1225, plain, (![A_187, B_188, C_189, D_190]: (k2_relset_1(A_187, B_188, C_189)=B_188 | ~r2_relset_1(B_188, B_188, k1_partfun1(B_188, A_187, A_187, B_188, D_190, C_189), k6_partfun1(B_188)) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(B_188, A_187))) | ~v1_funct_2(D_190, B_188, A_187) | ~v1_funct_1(D_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(C_189, A_187, B_188) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.53/1.77  tff(c_1231, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_635, c_1225])).
% 4.53/1.77  tff(c_1235, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_116, c_134, c_1231])).
% 4.53/1.77  tff(c_1237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_667, c_1235])).
% 4.53/1.77  tff(c_1238, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_662])).
% 4.53/1.77  tff(c_1239, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_662])).
% 4.53/1.77  tff(c_1240, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1239, c_134])).
% 4.53/1.77  tff(c_164, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_152])).
% 4.53/1.77  tff(c_214, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_205])).
% 4.53/1.77  tff(c_223, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_164, c_214])).
% 4.53/1.77  tff(c_224, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_223])).
% 4.53/1.77  tff(c_75, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_partfun1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 4.53/1.77  tff(c_1243, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_75])).
% 4.53/1.77  tff(c_1247, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_68, c_224, c_1243])).
% 4.53/1.77  tff(c_1255, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1247])).
% 4.53/1.77  tff(c_4, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.53/1.77  tff(c_76, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4])).
% 4.53/1.77  tff(c_1270, plain, (![C_203, B_199, F_202, E_200, D_198, A_201]: (k1_partfun1(A_201, B_199, C_203, D_198, E_200, F_202)=k5_relat_1(E_200, F_202) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(C_203, D_198))) | ~v1_funct_1(F_202) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_199))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.53/1.77  tff(c_1276, plain, (![A_201, B_199, E_200]: (k1_partfun1(A_201, B_199, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_199))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_64, c_1270])).
% 4.53/1.77  tff(c_1358, plain, (![A_215, B_216, E_217]: (k1_partfun1(A_215, B_216, '#skF_2', '#skF_1', E_217, '#skF_4')=k5_relat_1(E_217, '#skF_4') | ~m1_subset_1(E_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_1(E_217))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1276])).
% 4.53/1.77  tff(c_1364, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1358])).
% 4.53/1.77  tff(c_1371, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_635, c_1364])).
% 4.53/1.77  tff(c_6, plain, (![A_2, B_4]: (v2_funct_1(A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(k5_relat_1(B_4, A_2)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.53/1.77  tff(c_1381, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1371, c_6])).
% 4.53/1.77  tff(c_1387, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_68, c_107, c_74, c_76, c_133, c_224, c_1381])).
% 4.53/1.77  tff(c_1389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1255, c_1387])).
% 4.53/1.77  tff(c_1391, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1247])).
% 4.53/1.77  tff(c_1392, plain, (![B_218]: (k2_funct_1('#skF_4')=B_218 | k5_relat_1(B_218, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_218)!='#skF_2' | ~v1_funct_1(B_218) | ~v1_relat_1(B_218))), inference(splitRight, [status(thm)], [c_1247])).
% 4.53/1.77  tff(c_1398, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_107, c_1392])).
% 4.53/1.77  tff(c_1407, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_133, c_1398])).
% 4.53/1.77  tff(c_1409, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1407])).
% 4.53/1.77  tff(c_1464, plain, (![C_238, B_234, E_235, D_233, F_237, A_236]: (k1_partfun1(A_236, B_234, C_238, D_233, E_235, F_237)=k5_relat_1(E_235, F_237) | ~m1_subset_1(F_237, k1_zfmisc_1(k2_zfmisc_1(C_238, D_233))) | ~v1_funct_1(F_237) | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_234))) | ~v1_funct_1(E_235))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.53/1.77  tff(c_1470, plain, (![A_236, B_234, E_235]: (k1_partfun1(A_236, B_234, '#skF_2', '#skF_1', E_235, '#skF_4')=k5_relat_1(E_235, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_234))) | ~v1_funct_1(E_235))), inference(resolution, [status(thm)], [c_64, c_1464])).
% 4.53/1.77  tff(c_1484, plain, (![A_240, B_241, E_242]: (k1_partfun1(A_240, B_241, '#skF_2', '#skF_1', E_242, '#skF_4')=k5_relat_1(E_242, '#skF_4') | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(E_242))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1470])).
% 4.53/1.77  tff(c_1490, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1484])).
% 4.53/1.77  tff(c_1497, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_635, c_1490])).
% 4.53/1.77  tff(c_1499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1409, c_1497])).
% 4.53/1.77  tff(c_1500, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1407])).
% 4.53/1.77  tff(c_1646, plain, (![A_269, C_270, B_271]: (k6_partfun1(A_269)=k5_relat_1(C_270, k2_funct_1(C_270)) | k1_xboole_0=B_271 | ~v2_funct_1(C_270) | k2_relset_1(A_269, B_271, C_270)!=B_271 | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_269, B_271))) | ~v1_funct_2(C_270, A_269, B_271) | ~v1_funct_1(C_270))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.53/1.77  tff(c_1652, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1646])).
% 4.53/1.77  tff(c_1662, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1240, c_1391, c_1500, c_1652])).
% 4.53/1.77  tff(c_1664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1238, c_1662])).
% 4.53/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.77  
% 4.53/1.77  Inference rules
% 4.53/1.77  ----------------------
% 4.53/1.77  #Ref     : 0
% 4.53/1.77  #Sup     : 336
% 4.53/1.77  #Fact    : 0
% 4.53/1.77  #Define  : 0
% 4.53/1.77  #Split   : 17
% 4.53/1.77  #Chain   : 0
% 4.53/1.77  #Close   : 0
% 4.53/1.77  
% 4.53/1.77  Ordering : KBO
% 4.53/1.77  
% 4.53/1.77  Simplification rules
% 4.53/1.77  ----------------------
% 4.53/1.77  #Subsume      : 16
% 4.53/1.77  #Demod        : 372
% 4.53/1.77  #Tautology    : 89
% 4.53/1.77  #SimpNegUnit  : 35
% 4.53/1.77  #BackRed      : 16
% 4.53/1.77  
% 4.53/1.77  #Partial instantiations: 0
% 4.53/1.77  #Strategies tried      : 1
% 4.53/1.77  
% 4.53/1.78  Timing (in seconds)
% 4.53/1.78  ----------------------
% 4.53/1.78  Preprocessing        : 0.38
% 4.53/1.78  Parsing              : 0.20
% 4.53/1.78  CNF conversion       : 0.03
% 4.53/1.78  Main loop            : 0.62
% 4.53/1.78  Inferencing          : 0.22
% 4.53/1.78  Reduction            : 0.21
% 4.53/1.78  Demodulation         : 0.15
% 4.53/1.78  BG Simplification    : 0.03
% 4.53/1.78  Subsumption          : 0.12
% 4.53/1.78  Abstraction          : 0.03
% 4.53/1.78  MUC search           : 0.00
% 4.53/1.78  Cooper               : 0.00
% 4.53/1.78  Total                : 1.04
% 4.53/1.78  Index Insertion      : 0.00
% 4.53/1.78  Index Deletion       : 0.00
% 4.53/1.78  Index Matching       : 0.00
% 4.53/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
