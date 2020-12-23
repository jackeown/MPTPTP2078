%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:22 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  115 (1067 expanded)
%              Number of leaves         :   39 ( 446 expanded)
%              Depth                    :   20
%              Number of atoms          :  323 (6380 expanded)
%              Number of equality atoms :   88 (1846 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
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

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( B != k1_xboole_0
       => ( k2_relset_1(A,B,C) = B
        <=> ! [D] :
              ( D != k1_xboole_0
             => ! [E] :
                  ( ( v1_funct_1(E)
                    & v1_funct_2(E,B,D)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) )
                 => ! [F] :
                      ( ( v1_funct_1(F)
                        & v1_funct_2(F,B,D)
                        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(B,D))) )
                     => ( r2_relset_1(A,D,k1_partfun1(A,B,B,D,C,E),k1_partfun1(A,B,B,D,C,F))
                       => r2_relset_1(B,D,E,F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
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

tff(f_86,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_58,plain,(
    k2_funct_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_64,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    ! [C_54,B_53,A_52] :
      ( m1_subset_1(k2_funct_1(C_54),k1_zfmisc_1(k2_zfmisc_1(B_53,A_52)))
      | k2_relset_1(A_52,B_53,C_54) != B_53
      | ~ v2_funct_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_2(C_54,A_52,B_53)
      | ~ v1_funct_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_220,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_funct_1(k2_funct_1(C_86))
      | k2_relset_1(A_87,B_88,C_86) != B_88
      | ~ v2_funct_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_2(C_86,A_87,B_88)
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_223,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_220])).

tff(c_229,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_64,c_68,c_223])).

tff(c_270,plain,(
    ! [C_95,B_96,A_97] :
      ( v1_funct_2(k2_funct_1(C_95),B_96,A_97)
      | k2_relset_1(A_97,B_96,C_95) != B_96
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(C_95,A_97,B_96)
      | ~ v1_funct_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_273,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_270])).

tff(c_279,plain,(
    v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_64,c_68,c_273])).

tff(c_298,plain,(
    ! [C_101,B_102,A_103] :
      ( m1_subset_1(k2_funct_1(C_101),k1_zfmisc_1(k2_zfmisc_1(B_102,A_103)))
      | k2_relset_1(A_103,B_102,C_101) != B_102
      | ~ v2_funct_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102)))
      | ~ v1_funct_2(C_101,A_103,B_102)
      | ~ v1_funct_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    ! [A_24,B_25,C_26] :
      ( v1_funct_1('#skF_3'(A_24,B_25,C_26))
      | k2_relset_1(A_24,B_25,C_26) = B_25
      | k1_xboole_0 = B_25
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_917,plain,(
    ! [B_183,A_184,C_185] :
      ( v1_funct_1('#skF_3'(B_183,A_184,k2_funct_1(C_185)))
      | k2_relset_1(B_183,A_184,k2_funct_1(C_185)) = A_184
      | k1_xboole_0 = A_184
      | ~ v1_funct_2(k2_funct_1(C_185),B_183,A_184)
      | ~ v1_funct_1(k2_funct_1(C_185))
      | k2_relset_1(A_184,B_183,C_185) != B_183
      | ~ v2_funct_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183)))
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ v1_funct_1(C_185) ) ),
    inference(resolution,[status(thm)],[c_298,c_42])).

tff(c_929,plain,
    ( v1_funct_1('#skF_3'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_917])).

tff(c_938,plain,
    ( v1_funct_1('#skF_3'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_64,c_68,c_229,c_279,c_929])).

tff(c_939,plain,
    ( v1_funct_1('#skF_3'('#skF_5','#skF_4',k2_funct_1('#skF_6')))
    | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_938])).

tff(c_944,plain,(
    k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_939])).

tff(c_372,plain,(
    ! [A_108,D_111,F_110,B_109,C_107,E_112] :
      ( k1_partfun1(A_108,B_109,C_107,D_111,E_112,F_110) = k5_relat_1(E_112,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_107,D_111)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(E_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_376,plain,(
    ! [A_108,B_109,E_112] :
      ( k1_partfun1(A_108,B_109,'#skF_4','#skF_5',E_112,'#skF_6') = k5_relat_1(E_112,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(E_112) ) ),
    inference(resolution,[status(thm)],[c_76,c_372])).

tff(c_386,plain,(
    ! [A_113,B_114,E_115] :
      ( k1_partfun1(A_113,B_114,'#skF_4','#skF_5',E_115,'#skF_6') = k5_relat_1(E_115,'#skF_6')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_376])).

tff(c_481,plain,(
    ! [B_135,A_136,C_137] :
      ( k1_partfun1(B_135,A_136,'#skF_4','#skF_5',k2_funct_1(C_137),'#skF_6') = k5_relat_1(k2_funct_1(C_137),'#skF_6')
      | ~ v1_funct_1(k2_funct_1(C_137))
      | k2_relset_1(A_136,B_135,C_137) != B_135
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135)))
      | ~ v1_funct_2(C_137,A_136,B_135)
      | ~ v1_funct_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_52,c_386])).

tff(c_487,plain,
    ( k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),'#skF_6') = k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_481])).

tff(c_494,plain,(
    k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),'#skF_6') = k5_relat_1(k2_funct_1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_64,c_68,c_229,c_487])).

tff(c_976,plain,(
    ! [B_191,D_193,E_190,F_194,A_192,C_189] :
      ( r2_relset_1(B_191,D_193,E_190,F_194)
      | ~ r2_relset_1(A_192,D_193,k1_partfun1(A_192,B_191,B_191,D_193,C_189,E_190),k1_partfun1(A_192,B_191,B_191,D_193,C_189,F_194))
      | ~ m1_subset_1(F_194,k1_zfmisc_1(k2_zfmisc_1(B_191,D_193)))
      | ~ v1_funct_2(F_194,B_191,D_193)
      | ~ v1_funct_1(F_194)
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(B_191,D_193)))
      | ~ v1_funct_2(E_190,B_191,D_193)
      | ~ v1_funct_1(E_190)
      | k1_xboole_0 = D_193
      | k2_relset_1(A_192,B_191,C_189) != B_191
      | k1_xboole_0 = B_191
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191)))
      | ~ v1_funct_2(C_189,A_192,B_191)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_985,plain,(
    ! [E_190] :
      ( r2_relset_1('#skF_4','#skF_5',E_190,'#skF_6')
      | ~ r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),E_190),k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(E_190,'#skF_4','#skF_5')
      | ~ v1_funct_1(E_190)
      | k1_xboole_0 = '#skF_5'
      | k2_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_976])).

tff(c_1003,plain,(
    ! [E_190] :
      ( r2_relset_1('#skF_4','#skF_5',E_190,'#skF_6')
      | ~ r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),E_190),k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(E_190,'#skF_4','#skF_5')
      | ~ v1_funct_1(E_190)
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_279,c_944,c_80,c_78,c_76,c_985])).

tff(c_1004,plain,(
    ! [E_190] :
      ( r2_relset_1('#skF_4','#skF_5',E_190,'#skF_6')
      | ~ r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_4','#skF_4','#skF_5',k2_funct_1('#skF_6'),E_190),k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'))
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2(E_190,'#skF_4','#skF_5')
      | ~ v1_funct_1(E_190)
      | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60,c_1003])).

tff(c_1041,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1004])).

tff(c_1044,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1041])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_64,c_68,c_1044])).

tff(c_1050,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1004])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_76,c_97])).

tff(c_106,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_378,plain,(
    ! [A_108,B_109,E_112] :
      ( k1_partfun1(A_108,B_109,'#skF_5','#skF_4',E_112,'#skF_7') = k5_relat_1(E_112,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(E_112) ) ),
    inference(resolution,[status(thm)],[c_70,c_372])).

tff(c_412,plain,(
    ! [A_119,B_120,E_121] :
      ( k1_partfun1(A_119,B_120,'#skF_5','#skF_4',E_121,'#skF_7') = k5_relat_1(E_121,'#skF_7')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_378])).

tff(c_418,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_412])).

tff(c_425,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_418])).

tff(c_66,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_430,plain,(
    r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_66])).

tff(c_118,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_125,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_118])).

tff(c_156,plain,(
    ! [B_76,A_77,C_78] :
      ( k1_xboole_0 = B_76
      | k1_relset_1(A_77,B_76,C_78) = A_77
      | ~ v1_funct_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_159,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_156])).

tff(c_165,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_125,c_159])).

tff(c_166,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_165])).

tff(c_30,plain,(
    ! [A_23] : k6_relat_1(A_23) = k6_partfun1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_28,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] :
      ( k1_partfun1(A_17,B_18,C_19,D_20,E_21,F_22) = k5_relat_1(E_21,F_22)
      | ~ m1_subset_1(F_22,k1_zfmisc_1(k2_zfmisc_1(C_19,D_20)))
      | ~ v1_funct_1(F_22)
      | ~ m1_subset_1(E_21,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_1(E_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1094,plain,(
    ! [A_17,B_18,E_21] :
      ( k1_partfun1(A_17,B_18,'#skF_5','#skF_4',E_21,k2_funct_1('#skF_6')) = k5_relat_1(E_21,k2_funct_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ m1_subset_1(E_21,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_1(E_21) ) ),
    inference(resolution,[status(thm)],[c_1050,c_28])).

tff(c_1224,plain,(
    ! [A_199,B_200,E_201] :
      ( k1_partfun1(A_199,B_200,'#skF_5','#skF_4',E_201,k2_funct_1('#skF_6')) = k5_relat_1(E_201,k2_funct_1('#skF_6'))
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200)))
      | ~ v1_funct_1(E_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_1094])).

tff(c_1239,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',k2_funct_1('#skF_6')) = k5_relat_1('#skF_6',k2_funct_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_1224])).

tff(c_1251,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',k2_funct_1('#skF_6')) = k5_relat_1('#skF_6',k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1239])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_988,plain,(
    ! [F_194] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_194)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_194))
      | ~ m1_subset_1(F_194,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_194,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_194)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | k1_xboole_0 = '#skF_4'
      | k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_976])).

tff(c_1006,plain,(
    ! [F_194] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_194)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_194))
      | ~ m1_subset_1(F_194,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_194,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_194)
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_68,c_74,c_72,c_70,c_988])).

tff(c_1007,plain,(
    ! [F_194] :
      ( r2_relset_1('#skF_5','#skF_4','#skF_7',F_194)
      | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6',F_194))
      | ~ m1_subset_1(F_194,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
      | ~ v1_funct_2(F_194,'#skF_5','#skF_4')
      | ~ v1_funct_1(F_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_62,c_1006])).

tff(c_1295,plain,
    ( r2_relset_1('#skF_5','#skF_4','#skF_7',k2_funct_1('#skF_6'))
    | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k5_relat_1('#skF_6',k2_funct_1('#skF_6')))
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1251,c_1007])).

tff(c_1307,plain,
    ( r2_relset_1('#skF_5','#skF_4','#skF_7',k2_funct_1('#skF_6'))
    | ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k5_relat_1('#skF_6',k2_funct_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_279,c_1050,c_1295])).

tff(c_1345,plain,(
    ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k5_relat_1('#skF_6',k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1307])).

tff(c_1348,plain,
    ( ~ r2_relset_1('#skF_4','#skF_4',k5_relat_1('#skF_6','#skF_7'),k6_partfun1(k1_relat_1('#skF_6')))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_1345])).

tff(c_1351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_80,c_64,c_430,c_166,c_1348])).

tff(c_1352,plain,(
    r2_relset_1('#skF_5','#skF_4','#skF_7',k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1307])).

tff(c_14,plain,(
    ! [D_13,C_12,A_10,B_11] :
      ( D_13 = C_12
      | ~ r2_relset_1(A_10,B_11,C_12,D_13)
      | ~ m1_subset_1(D_13,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1356,plain,
    ( k2_funct_1('#skF_6') = '#skF_7'
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1352,c_14])).

tff(c_1359,plain,(
    k2_funct_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1050,c_1356])).

tff(c_1361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.81  
% 4.42/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.82  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 4.47/1.82  
% 4.47/1.82  %Foreground sorts:
% 4.47/1.82  
% 4.47/1.82  
% 4.47/1.82  %Background operators:
% 4.47/1.82  
% 4.47/1.82  
% 4.47/1.82  %Foreground operators:
% 4.47/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.47/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.47/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.47/1.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.47/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.47/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.47/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.82  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.47/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.47/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.47/1.82  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.47/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.47/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.47/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.47/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.47/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.82  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.47/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.47/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.47/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.47/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.47/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.47/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.82  
% 4.47/1.84  tff(f_161, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.47/1.84  tff(f_135, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.47/1.84  tff(f_119, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => ((k2_relset_1(A, B, C) = B) <=> (![D]: (~(D = k1_xboole_0) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, B, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(B, D)))) => (r2_relset_1(A, D, k1_partfun1(A, B, B, D, C, E), k1_partfun1(A, B, B, D, C, F)) => r2_relset_1(B, D, E, F)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_2)).
% 4.47/1.84  tff(f_84, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.47/1.84  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.47/1.84  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.47/1.84  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.47/1.84  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.47/1.84  tff(f_86, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.47/1.84  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.47/1.84  tff(f_56, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.47/1.84  tff(c_58, plain, (k2_funct_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_64, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_68, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_52, plain, (![C_54, B_53, A_52]: (m1_subset_1(k2_funct_1(C_54), k1_zfmisc_1(k2_zfmisc_1(B_53, A_52))) | k2_relset_1(A_52, B_53, C_54)!=B_53 | ~v2_funct_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_2(C_54, A_52, B_53) | ~v1_funct_1(C_54))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.47/1.84  tff(c_62, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_60, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_220, plain, (![C_86, A_87, B_88]: (v1_funct_1(k2_funct_1(C_86)) | k2_relset_1(A_87, B_88, C_86)!=B_88 | ~v2_funct_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_2(C_86, A_87, B_88) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.47/1.84  tff(c_223, plain, (v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_220])).
% 4.47/1.84  tff(c_229, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_64, c_68, c_223])).
% 4.47/1.84  tff(c_270, plain, (![C_95, B_96, A_97]: (v1_funct_2(k2_funct_1(C_95), B_96, A_97) | k2_relset_1(A_97, B_96, C_95)!=B_96 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(C_95, A_97, B_96) | ~v1_funct_1(C_95))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.47/1.84  tff(c_273, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_270])).
% 4.47/1.84  tff(c_279, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_64, c_68, c_273])).
% 4.47/1.84  tff(c_298, plain, (![C_101, B_102, A_103]: (m1_subset_1(k2_funct_1(C_101), k1_zfmisc_1(k2_zfmisc_1(B_102, A_103))) | k2_relset_1(A_103, B_102, C_101)!=B_102 | ~v2_funct_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))) | ~v1_funct_2(C_101, A_103, B_102) | ~v1_funct_1(C_101))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.47/1.84  tff(c_42, plain, (![A_24, B_25, C_26]: (v1_funct_1('#skF_3'(A_24, B_25, C_26)) | k2_relset_1(A_24, B_25, C_26)=B_25 | k1_xboole_0=B_25 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.47/1.84  tff(c_917, plain, (![B_183, A_184, C_185]: (v1_funct_1('#skF_3'(B_183, A_184, k2_funct_1(C_185))) | k2_relset_1(B_183, A_184, k2_funct_1(C_185))=A_184 | k1_xboole_0=A_184 | ~v1_funct_2(k2_funct_1(C_185), B_183, A_184) | ~v1_funct_1(k2_funct_1(C_185)) | k2_relset_1(A_184, B_183, C_185)!=B_183 | ~v2_funct_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))) | ~v1_funct_2(C_185, A_184, B_183) | ~v1_funct_1(C_185))), inference(resolution, [status(thm)], [c_298, c_42])).
% 4.47/1.84  tff(c_929, plain, (v1_funct_1('#skF_3'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4' | k1_xboole_0='#skF_4' | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_917])).
% 4.47/1.84  tff(c_938, plain, (v1_funct_1('#skF_3'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_64, c_68, c_229, c_279, c_929])).
% 4.47/1.84  tff(c_939, plain, (v1_funct_1('#skF_3'('#skF_5', '#skF_4', k2_funct_1('#skF_6'))) | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_62, c_938])).
% 4.47/1.84  tff(c_944, plain, (k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))='#skF_4'), inference(splitLeft, [status(thm)], [c_939])).
% 4.47/1.84  tff(c_372, plain, (![A_108, D_111, F_110, B_109, C_107, E_112]: (k1_partfun1(A_108, B_109, C_107, D_111, E_112, F_110)=k5_relat_1(E_112, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_107, D_111))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(E_112))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.47/1.84  tff(c_376, plain, (![A_108, B_109, E_112]: (k1_partfun1(A_108, B_109, '#skF_4', '#skF_5', E_112, '#skF_6')=k5_relat_1(E_112, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(E_112))), inference(resolution, [status(thm)], [c_76, c_372])).
% 4.47/1.84  tff(c_386, plain, (![A_113, B_114, E_115]: (k1_partfun1(A_113, B_114, '#skF_4', '#skF_5', E_115, '#skF_6')=k5_relat_1(E_115, '#skF_6') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_115))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_376])).
% 4.47/1.84  tff(c_481, plain, (![B_135, A_136, C_137]: (k1_partfun1(B_135, A_136, '#skF_4', '#skF_5', k2_funct_1(C_137), '#skF_6')=k5_relat_1(k2_funct_1(C_137), '#skF_6') | ~v1_funct_1(k2_funct_1(C_137)) | k2_relset_1(A_136, B_135, C_137)!=B_135 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))) | ~v1_funct_2(C_137, A_136, B_135) | ~v1_funct_1(C_137))), inference(resolution, [status(thm)], [c_52, c_386])).
% 4.47/1.84  tff(c_487, plain, (k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), '#skF_6')=k5_relat_1(k2_funct_1('#skF_6'), '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_481])).
% 4.47/1.84  tff(c_494, plain, (k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), '#skF_6')=k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_64, c_68, c_229, c_487])).
% 4.47/1.84  tff(c_976, plain, (![B_191, D_193, E_190, F_194, A_192, C_189]: (r2_relset_1(B_191, D_193, E_190, F_194) | ~r2_relset_1(A_192, D_193, k1_partfun1(A_192, B_191, B_191, D_193, C_189, E_190), k1_partfun1(A_192, B_191, B_191, D_193, C_189, F_194)) | ~m1_subset_1(F_194, k1_zfmisc_1(k2_zfmisc_1(B_191, D_193))) | ~v1_funct_2(F_194, B_191, D_193) | ~v1_funct_1(F_194) | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(B_191, D_193))) | ~v1_funct_2(E_190, B_191, D_193) | ~v1_funct_1(E_190) | k1_xboole_0=D_193 | k2_relset_1(A_192, B_191, C_189)!=B_191 | k1_xboole_0=B_191 | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))) | ~v1_funct_2(C_189, A_192, B_191) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.47/1.84  tff(c_985, plain, (![E_190]: (r2_relset_1('#skF_4', '#skF_5', E_190, '#skF_6') | ~r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), E_190), k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(E_190, '#skF_4', '#skF_5') | ~v1_funct_1(E_190) | k1_xboole_0='#skF_5' | k2_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_4' | k1_xboole_0='#skF_4' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_494, c_976])).
% 4.47/1.84  tff(c_1003, plain, (![E_190]: (r2_relset_1('#skF_4', '#skF_5', E_190, '#skF_6') | ~r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), E_190), k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')) | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(E_190, '#skF_4', '#skF_5') | ~v1_funct_1(E_190) | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_279, c_944, c_80, c_78, c_76, c_985])).
% 4.47/1.84  tff(c_1004, plain, (![E_190]: (r2_relset_1('#skF_4', '#skF_5', E_190, '#skF_6') | ~r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_4', '#skF_4', '#skF_5', k2_funct_1('#skF_6'), E_190), k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')) | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(E_190, '#skF_4', '#skF_5') | ~v1_funct_1(E_190) | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_60, c_1003])).
% 4.47/1.84  tff(c_1041, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1004])).
% 4.47/1.84  tff(c_1044, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_1041])).
% 4.47/1.84  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_64, c_68, c_1044])).
% 4.47/1.84  tff(c_1050, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_1004])).
% 4.47/1.84  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.47/1.84  tff(c_97, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.84  tff(c_100, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_76, c_97])).
% 4.47/1.84  tff(c_106, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 4.47/1.84  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_378, plain, (![A_108, B_109, E_112]: (k1_partfun1(A_108, B_109, '#skF_5', '#skF_4', E_112, '#skF_7')=k5_relat_1(E_112, '#skF_7') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(E_112))), inference(resolution, [status(thm)], [c_70, c_372])).
% 4.47/1.84  tff(c_412, plain, (![A_119, B_120, E_121]: (k1_partfun1(A_119, B_120, '#skF_5', '#skF_4', E_121, '#skF_7')=k5_relat_1(E_121, '#skF_7') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_121))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_378])).
% 4.47/1.84  tff(c_418, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_412])).
% 4.47/1.84  tff(c_425, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k5_relat_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_418])).
% 4.47/1.84  tff(c_66, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_430, plain, (r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_66])).
% 4.47/1.84  tff(c_118, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.47/1.84  tff(c_125, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_118])).
% 4.47/1.84  tff(c_156, plain, (![B_76, A_77, C_78]: (k1_xboole_0=B_76 | k1_relset_1(A_77, B_76, C_78)=A_77 | ~v1_funct_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.47/1.84  tff(c_159, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_156])).
% 4.47/1.84  tff(c_165, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_125, c_159])).
% 4.47/1.84  tff(c_166, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_60, c_165])).
% 4.47/1.84  tff(c_30, plain, (![A_23]: (k6_relat_1(A_23)=k6_partfun1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.47/1.84  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.47/1.84  tff(c_81, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8])).
% 4.47/1.84  tff(c_28, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (k1_partfun1(A_17, B_18, C_19, D_20, E_21, F_22)=k5_relat_1(E_21, F_22) | ~m1_subset_1(F_22, k1_zfmisc_1(k2_zfmisc_1(C_19, D_20))) | ~v1_funct_1(F_22) | ~m1_subset_1(E_21, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_1(E_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.47/1.84  tff(c_1094, plain, (![A_17, B_18, E_21]: (k1_partfun1(A_17, B_18, '#skF_5', '#skF_4', E_21, k2_funct_1('#skF_6'))=k5_relat_1(E_21, k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~m1_subset_1(E_21, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_1(E_21))), inference(resolution, [status(thm)], [c_1050, c_28])).
% 4.47/1.84  tff(c_1224, plain, (![A_199, B_200, E_201]: (k1_partfun1(A_199, B_200, '#skF_5', '#skF_4', E_201, k2_funct_1('#skF_6'))=k5_relat_1(E_201, k2_funct_1('#skF_6')) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))) | ~v1_funct_1(E_201))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_1094])).
% 4.47/1.84  tff(c_1239, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', k2_funct_1('#skF_6'))=k5_relat_1('#skF_6', k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_1224])).
% 4.47/1.84  tff(c_1251, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', k2_funct_1('#skF_6'))=k5_relat_1('#skF_6', k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1239])).
% 4.47/1.84  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.47/1.84  tff(c_988, plain, (![F_194]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_194) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_194)) | ~m1_subset_1(F_194, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_194, '#skF_5', '#skF_4') | ~v1_funct_1(F_194) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | k1_xboole_0='#skF_4' | k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_976])).
% 4.47/1.84  tff(c_1006, plain, (![F_194]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_194) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_194)) | ~m1_subset_1(F_194, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_194, '#skF_5', '#skF_4') | ~v1_funct_1(F_194) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_68, c_74, c_72, c_70, c_988])).
% 4.47/1.84  tff(c_1007, plain, (![F_194]: (r2_relset_1('#skF_5', '#skF_4', '#skF_7', F_194) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', F_194)) | ~m1_subset_1(F_194, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(F_194, '#skF_5', '#skF_4') | ~v1_funct_1(F_194))), inference(negUnitSimplification, [status(thm)], [c_60, c_62, c_1006])).
% 4.47/1.84  tff(c_1295, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', k2_funct_1('#skF_6')) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k5_relat_1('#skF_6', k2_funct_1('#skF_6'))) | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1251, c_1007])).
% 4.47/1.84  tff(c_1307, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', k2_funct_1('#skF_6')) | ~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k5_relat_1('#skF_6', k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_279, c_1050, c_1295])).
% 4.47/1.84  tff(c_1345, plain, (~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k5_relat_1('#skF_6', k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_1307])).
% 4.47/1.84  tff(c_1348, plain, (~r2_relset_1('#skF_4', '#skF_4', k5_relat_1('#skF_6', '#skF_7'), k6_partfun1(k1_relat_1('#skF_6'))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_81, c_1345])).
% 4.47/1.84  tff(c_1351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_80, c_64, c_430, c_166, c_1348])).
% 4.47/1.84  tff(c_1352, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1307])).
% 4.47/1.84  tff(c_14, plain, (![D_13, C_12, A_10, B_11]: (D_13=C_12 | ~r2_relset_1(A_10, B_11, C_12, D_13) | ~m1_subset_1(D_13, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.47/1.84  tff(c_1356, plain, (k2_funct_1('#skF_6')='#skF_7' | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_1352, c_14])).
% 4.47/1.84  tff(c_1359, plain, (k2_funct_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1050, c_1356])).
% 4.47/1.84  tff(c_1361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1359])).
% 4.47/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.84  
% 4.47/1.84  Inference rules
% 4.47/1.84  ----------------------
% 4.47/1.84  #Ref     : 0
% 4.47/1.84  #Sup     : 264
% 4.47/1.84  #Fact    : 0
% 4.47/1.84  #Define  : 0
% 4.47/1.84  #Split   : 8
% 4.47/1.84  #Chain   : 0
% 4.47/1.84  #Close   : 0
% 4.47/1.84  
% 4.47/1.84  Ordering : KBO
% 4.47/1.84  
% 4.47/1.84  Simplification rules
% 4.47/1.84  ----------------------
% 4.47/1.84  #Subsume      : 31
% 4.47/1.84  #Demod        : 354
% 4.47/1.84  #Tautology    : 97
% 4.47/1.84  #SimpNegUnit  : 51
% 4.47/1.84  #BackRed      : 5
% 4.47/1.84  
% 4.47/1.84  #Partial instantiations: 0
% 4.47/1.84  #Strategies tried      : 1
% 4.47/1.84  
% 4.47/1.84  Timing (in seconds)
% 4.47/1.84  ----------------------
% 4.47/1.84  Preprocessing        : 0.36
% 4.47/1.84  Parsing              : 0.18
% 4.47/1.84  CNF conversion       : 0.03
% 4.47/1.84  Main loop            : 0.68
% 4.47/1.84  Inferencing          : 0.21
% 4.47/1.84  Reduction            : 0.22
% 4.47/1.84  Demodulation         : 0.16
% 4.47/1.84  BG Simplification    : 0.05
% 4.47/1.84  Subsumption          : 0.15
% 4.47/1.84  Abstraction          : 0.04
% 4.47/1.84  MUC search           : 0.00
% 4.47/1.84  Cooper               : 0.00
% 4.47/1.84  Total                : 1.08
% 4.47/1.84  Index Insertion      : 0.00
% 4.47/1.84  Index Deletion       : 0.00
% 4.47/1.84  Index Matching       : 0.00
% 4.47/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
