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
% DateTime   : Thu Dec  3 10:13:20 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 718 expanded)
%              Number of leaves         :   41 ( 271 expanded)
%              Depth                    :   18
%              Number of atoms          :  322 (2959 expanded)
%              Number of equality atoms :  113 (1046 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_183,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_140,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_72,axiom,(
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

tff(f_98,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_157,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_55,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_94,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_94])).

tff(c_112,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_172,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_184,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_172])).

tff(c_226,plain,(
    ! [B_75,A_76,C_77] :
      ( k1_xboole_0 = B_75
      | k1_relset_1(A_76,B_75,C_77) = A_76
      | ~ v1_funct_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_235,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_226])).

tff(c_244,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_184,c_235])).

tff(c_245,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_244])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_100,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_94])).

tff(c_109,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_183,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_172])).

tff(c_232,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_226])).

tff(c_240,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_183,c_232])).

tff(c_241,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_240])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_141,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_relset_1(A_60,B_61,C_62) = k2_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_147,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_141])).

tff(c_153,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_147])).

tff(c_46,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_528,plain,(
    ! [A_123,B_124] :
      ( k2_funct_1(A_123) = B_124
      | k6_partfun1(k2_relat_1(A_123)) != k5_relat_1(B_124,A_123)
      | k2_relat_1(B_124) != k1_relat_1(A_123)
      | ~ v2_funct_1(A_123)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_530,plain,(
    ! [B_124] :
      ( k2_funct_1('#skF_3') = B_124
      | k5_relat_1(B_124,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_124) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_528])).

tff(c_533,plain,(
    ! [B_125] :
      ( k2_funct_1('#skF_3') = B_125
      | k5_relat_1(B_125,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_125) != '#skF_1'
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_72,c_56,c_241,c_530])).

tff(c_536,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_533])).

tff(c_548,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_536])).

tff(c_549,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_548])).

tff(c_555,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_26,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_73,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_26])).

tff(c_130,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_137,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_73,c_130])).

tff(c_154,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_141])).

tff(c_399,plain,(
    ! [B_111,D_108,F_109,E_110,A_107,C_112] :
      ( k1_partfun1(A_107,B_111,C_112,D_108,E_110,F_109) = k5_relat_1(E_110,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_112,D_108)))
      | ~ v1_funct_1(F_109)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_107,B_111)))
      | ~ v1_funct_1(E_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_405,plain,(
    ! [A_107,B_111,E_110] :
      ( k1_partfun1(A_107,B_111,'#skF_2','#skF_1',E_110,'#skF_4') = k5_relat_1(E_110,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_107,B_111)))
      | ~ v1_funct_1(E_110) ) ),
    inference(resolution,[status(thm)],[c_62,c_399])).

tff(c_414,plain,(
    ! [A_114,B_115,E_116] :
      ( k1_partfun1(A_114,B_115,'#skF_2','#skF_1',E_116,'#skF_4') = k5_relat_1(E_116,'#skF_4')
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_1(E_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_405])).

tff(c_420,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_414])).

tff(c_427,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_420])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_296,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_304,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_296])).

tff(c_319,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_304])).

tff(c_320,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_432,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_320])).

tff(c_448,plain,(
    ! [D_122,A_119,B_121,F_117,C_120,E_118] :
      ( m1_subset_1(k1_partfun1(A_119,B_121,C_120,D_122,E_118,F_117),k1_zfmisc_1(k2_zfmisc_1(A_119,D_122)))
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_120,D_122)))
      | ~ v1_funct_1(F_117)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_121)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_496,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_448])).

tff(c_516,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_496])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_516])).

tff(c_519,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_887,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k2_relset_1(A_157,B_158,C_159) = B_158
      | ~ r2_relset_1(B_158,B_158,k1_partfun1(B_158,A_157,A_157,B_158,D_160,C_159),k6_partfun1(B_158))
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(B_158,A_157)))
      | ~ v1_funct_2(D_160,B_158,A_157)
      | ~ v1_funct_1(D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ v1_funct_2(C_159,A_157,B_158)
      | ~ v1_funct_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_890,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_887])).

tff(c_892,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_137,c_154,c_890])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_892])).

tff(c_896,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_74,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_partfun1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_900,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_74])).

tff(c_904,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_66,c_245,c_900])).

tff(c_912,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_904])).

tff(c_8,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_969,plain,(
    ! [A_178,D_179,E_181,F_180,C_183,B_182] :
      ( k1_partfun1(A_178,B_182,C_183,D_179,E_181,F_180) = k5_relat_1(E_181,F_180)
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(C_183,D_179)))
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_178,B_182)))
      | ~ v1_funct_1(E_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_975,plain,(
    ! [A_178,B_182,E_181] :
      ( k1_partfun1(A_178,B_182,'#skF_2','#skF_1',E_181,'#skF_4') = k5_relat_1(E_181,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(A_178,B_182)))
      | ~ v1_funct_1(E_181) ) ),
    inference(resolution,[status(thm)],[c_62,c_969])).

tff(c_983,plain,(
    ! [A_184,B_185,E_186] :
      ( k1_partfun1(A_184,B_185,'#skF_2','#skF_1',E_186,'#skF_4') = k5_relat_1(E_186,'#skF_4')
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ v1_funct_1(E_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_975])).

tff(c_989,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_983])).

tff(c_996,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_519,c_989])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( v2_funct_1(A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(k5_relat_1(B_9,A_7))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1006,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_10])).

tff(c_1012,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_66,c_109,c_72,c_75,c_153,c_245,c_1006])).

tff(c_1014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_912,c_1012])).

tff(c_1016,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_904])).

tff(c_1017,plain,(
    ! [B_187] :
      ( k2_funct_1('#skF_4') = B_187
      | k5_relat_1(B_187,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_187) != '#skF_2'
      | ~ v1_funct_1(B_187)
      | ~ v1_relat_1(B_187) ) ),
    inference(splitRight,[status(thm)],[c_904])).

tff(c_1023,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_1017])).

tff(c_1035,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_153,c_1023])).

tff(c_1038,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1035])).

tff(c_1100,plain,(
    ! [B_209,C_210,A_205,F_207,E_208,D_206] :
      ( k1_partfun1(A_205,B_209,C_210,D_206,E_208,F_207) = k5_relat_1(E_208,F_207)
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(C_210,D_206)))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_205,B_209)))
      | ~ v1_funct_1(E_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1106,plain,(
    ! [A_205,B_209,E_208] :
      ( k1_partfun1(A_205,B_209,'#skF_2','#skF_1',E_208,'#skF_4') = k5_relat_1(E_208,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_205,B_209)))
      | ~ v1_funct_1(E_208) ) ),
    inference(resolution,[status(thm)],[c_62,c_1100])).

tff(c_1397,plain,(
    ! [A_225,B_226,E_227] :
      ( k1_partfun1(A_225,B_226,'#skF_2','#skF_1',E_227,'#skF_4') = k5_relat_1(E_227,'#skF_4')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ v1_funct_1(E_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1106])).

tff(c_1412,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1397])).

tff(c_1426,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_519,c_1412])).

tff(c_1428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1038,c_1426])).

tff(c_1429,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1035])).

tff(c_16,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1435,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_16])).

tff(c_1439,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_66,c_1016,c_1435])).

tff(c_1441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:43:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.74  
% 3.98/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.74  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.98/1.74  
% 3.98/1.74  %Foreground sorts:
% 3.98/1.74  
% 3.98/1.74  
% 3.98/1.74  %Background operators:
% 3.98/1.74  
% 3.98/1.74  
% 3.98/1.74  %Foreground operators:
% 3.98/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.98/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.98/1.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.98/1.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.98/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.74  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.98/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.98/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.98/1.74  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.98/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.98/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.98/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.74  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.98/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.98/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.74  tff('#skF_4', type, '#skF_4': $i).
% 3.98/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.98/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.98/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.74  
% 3.98/1.77  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 3.98/1.77  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.98/1.77  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.98/1.77  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.98/1.77  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.98/1.77  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.98/1.77  tff(f_140, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.98/1.77  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 3.98/1.77  tff(f_98, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.98/1.77  tff(f_96, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.98/1.77  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.98/1.77  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.98/1.77  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.98/1.77  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.98/1.77  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 3.98/1.77  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.98/1.77  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.98/1.77  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_94, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.98/1.77  tff(c_103, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_94])).
% 3.98/1.77  tff(c_112, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_103])).
% 3.98/1.77  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_172, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.98/1.77  tff(c_184, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_172])).
% 3.98/1.77  tff(c_226, plain, (![B_75, A_76, C_77]: (k1_xboole_0=B_75 | k1_relset_1(A_76, B_75, C_77)=A_76 | ~v1_funct_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.98/1.77  tff(c_235, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_226])).
% 3.98/1.77  tff(c_244, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_184, c_235])).
% 3.98/1.77  tff(c_245, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_244])).
% 3.98/1.77  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_100, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_94])).
% 3.98/1.77  tff(c_109, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 3.98/1.77  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_183, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_172])).
% 3.98/1.77  tff(c_232, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_226])).
% 3.98/1.77  tff(c_240, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_183, c_232])).
% 3.98/1.77  tff(c_241, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_240])).
% 3.98/1.77  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_141, plain, (![A_60, B_61, C_62]: (k2_relset_1(A_60, B_61, C_62)=k2_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.98/1.77  tff(c_147, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_141])).
% 3.98/1.77  tff(c_153, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_147])).
% 3.98/1.77  tff(c_46, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.98/1.77  tff(c_14, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.98/1.77  tff(c_528, plain, (![A_123, B_124]: (k2_funct_1(A_123)=B_124 | k6_partfun1(k2_relat_1(A_123))!=k5_relat_1(B_124, A_123) | k2_relat_1(B_124)!=k1_relat_1(A_123) | ~v2_funct_1(A_123) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 3.98/1.77  tff(c_530, plain, (![B_124]: (k2_funct_1('#skF_3')=B_124 | k5_relat_1(B_124, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_124)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_528])).
% 3.98/1.77  tff(c_533, plain, (![B_125]: (k2_funct_1('#skF_3')=B_125 | k5_relat_1(B_125, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_125)!='#skF_1' | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_72, c_56, c_241, c_530])).
% 3.98/1.77  tff(c_536, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_112, c_533])).
% 3.98/1.77  tff(c_548, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_536])).
% 3.98/1.77  tff(c_549, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_548])).
% 3.98/1.77  tff(c_555, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_549])).
% 3.98/1.77  tff(c_26, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.98/1.77  tff(c_73, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_26])).
% 3.98/1.77  tff(c_130, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.98/1.77  tff(c_137, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_73, c_130])).
% 3.98/1.77  tff(c_154, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_141])).
% 3.98/1.77  tff(c_399, plain, (![B_111, D_108, F_109, E_110, A_107, C_112]: (k1_partfun1(A_107, B_111, C_112, D_108, E_110, F_109)=k5_relat_1(E_110, F_109) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(C_112, D_108))) | ~v1_funct_1(F_109) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_107, B_111))) | ~v1_funct_1(E_110))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.98/1.77  tff(c_405, plain, (![A_107, B_111, E_110]: (k1_partfun1(A_107, B_111, '#skF_2', '#skF_1', E_110, '#skF_4')=k5_relat_1(E_110, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_107, B_111))) | ~v1_funct_1(E_110))), inference(resolution, [status(thm)], [c_62, c_399])).
% 3.98/1.77  tff(c_414, plain, (![A_114, B_115, E_116]: (k1_partfun1(A_114, B_115, '#skF_2', '#skF_1', E_116, '#skF_4')=k5_relat_1(E_116, '#skF_4') | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_1(E_116))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_405])).
% 3.98/1.77  tff(c_420, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_414])).
% 3.98/1.77  tff(c_427, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_420])).
% 3.98/1.77  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.98/1.77  tff(c_296, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.98/1.77  tff(c_304, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_296])).
% 3.98/1.77  tff(c_319, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_304])).
% 3.98/1.77  tff(c_320, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_319])).
% 3.98/1.77  tff(c_432, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_320])).
% 3.98/1.77  tff(c_448, plain, (![D_122, A_119, B_121, F_117, C_120, E_118]: (m1_subset_1(k1_partfun1(A_119, B_121, C_120, D_122, E_118, F_117), k1_zfmisc_1(k2_zfmisc_1(A_119, D_122))) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_120, D_122))) | ~v1_funct_1(F_117) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_121))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.98/1.77  tff(c_496, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_427, c_448])).
% 3.98/1.77  tff(c_516, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_496])).
% 3.98/1.77  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_432, c_516])).
% 3.98/1.77  tff(c_519, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_319])).
% 3.98/1.77  tff(c_887, plain, (![A_157, B_158, C_159, D_160]: (k2_relset_1(A_157, B_158, C_159)=B_158 | ~r2_relset_1(B_158, B_158, k1_partfun1(B_158, A_157, A_157, B_158, D_160, C_159), k6_partfun1(B_158)) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(B_158, A_157))) | ~v1_funct_2(D_160, B_158, A_157) | ~v1_funct_1(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~v1_funct_2(C_159, A_157, B_158) | ~v1_funct_1(C_159))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.98/1.77  tff(c_890, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_519, c_887])).
% 3.98/1.77  tff(c_892, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_137, c_154, c_890])).
% 3.98/1.77  tff(c_894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_555, c_892])).
% 3.98/1.77  tff(c_896, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_549])).
% 3.98/1.77  tff(c_74, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_partfun1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 3.98/1.77  tff(c_900, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_896, c_74])).
% 3.98/1.77  tff(c_904, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_66, c_245, c_900])).
% 3.98/1.77  tff(c_912, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_904])).
% 3.98/1.77  tff(c_8, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.98/1.77  tff(c_75, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 3.98/1.77  tff(c_969, plain, (![A_178, D_179, E_181, F_180, C_183, B_182]: (k1_partfun1(A_178, B_182, C_183, D_179, E_181, F_180)=k5_relat_1(E_181, F_180) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(C_183, D_179))) | ~v1_funct_1(F_180) | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(A_178, B_182))) | ~v1_funct_1(E_181))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.98/1.77  tff(c_975, plain, (![A_178, B_182, E_181]: (k1_partfun1(A_178, B_182, '#skF_2', '#skF_1', E_181, '#skF_4')=k5_relat_1(E_181, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(A_178, B_182))) | ~v1_funct_1(E_181))), inference(resolution, [status(thm)], [c_62, c_969])).
% 3.98/1.77  tff(c_983, plain, (![A_184, B_185, E_186]: (k1_partfun1(A_184, B_185, '#skF_2', '#skF_1', E_186, '#skF_4')=k5_relat_1(E_186, '#skF_4') | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~v1_funct_1(E_186))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_975])).
% 3.98/1.77  tff(c_989, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_983])).
% 3.98/1.77  tff(c_996, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_519, c_989])).
% 3.98/1.77  tff(c_10, plain, (![A_7, B_9]: (v2_funct_1(A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(k5_relat_1(B_9, A_7)) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.98/1.77  tff(c_1006, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_996, c_10])).
% 3.98/1.77  tff(c_1012, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_66, c_109, c_72, c_75, c_153, c_245, c_1006])).
% 3.98/1.77  tff(c_1014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_912, c_1012])).
% 3.98/1.77  tff(c_1016, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_904])).
% 3.98/1.77  tff(c_1017, plain, (![B_187]: (k2_funct_1('#skF_4')=B_187 | k5_relat_1(B_187, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_187)!='#skF_2' | ~v1_funct_1(B_187) | ~v1_relat_1(B_187))), inference(splitRight, [status(thm)], [c_904])).
% 3.98/1.77  tff(c_1023, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_1017])).
% 3.98/1.77  tff(c_1035, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_153, c_1023])).
% 3.98/1.77  tff(c_1038, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1035])).
% 3.98/1.77  tff(c_1100, plain, (![B_209, C_210, A_205, F_207, E_208, D_206]: (k1_partfun1(A_205, B_209, C_210, D_206, E_208, F_207)=k5_relat_1(E_208, F_207) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(C_210, D_206))) | ~v1_funct_1(F_207) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_205, B_209))) | ~v1_funct_1(E_208))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.98/1.77  tff(c_1106, plain, (![A_205, B_209, E_208]: (k1_partfun1(A_205, B_209, '#skF_2', '#skF_1', E_208, '#skF_4')=k5_relat_1(E_208, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_205, B_209))) | ~v1_funct_1(E_208))), inference(resolution, [status(thm)], [c_62, c_1100])).
% 3.98/1.77  tff(c_1397, plain, (![A_225, B_226, E_227]: (k1_partfun1(A_225, B_226, '#skF_2', '#skF_1', E_227, '#skF_4')=k5_relat_1(E_227, '#skF_4') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~v1_funct_1(E_227))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1106])).
% 3.98/1.77  tff(c_1412, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1397])).
% 3.98/1.77  tff(c_1426, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_519, c_1412])).
% 3.98/1.77  tff(c_1428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1038, c_1426])).
% 3.98/1.77  tff(c_1429, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1035])).
% 3.98/1.77  tff(c_16, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.98/1.77  tff(c_1435, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1429, c_16])).
% 3.98/1.77  tff(c_1439, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_66, c_1016, c_1435])).
% 3.98/1.77  tff(c_1441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1439])).
% 3.98/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.77  
% 3.98/1.77  Inference rules
% 3.98/1.77  ----------------------
% 3.98/1.77  #Ref     : 0
% 3.98/1.77  #Sup     : 287
% 3.98/1.77  #Fact    : 0
% 3.98/1.77  #Define  : 0
% 3.98/1.77  #Split   : 16
% 3.98/1.77  #Chain   : 0
% 3.98/1.77  #Close   : 0
% 3.98/1.77  
% 3.98/1.77  Ordering : KBO
% 3.98/1.77  
% 3.98/1.77  Simplification rules
% 3.98/1.77  ----------------------
% 3.98/1.77  #Subsume      : 2
% 3.98/1.77  #Demod        : 240
% 3.98/1.77  #Tautology    : 77
% 3.98/1.77  #SimpNegUnit  : 20
% 3.98/1.77  #BackRed      : 13
% 3.98/1.77  
% 3.98/1.77  #Partial instantiations: 0
% 3.98/1.77  #Strategies tried      : 1
% 3.98/1.77  
% 3.98/1.77  Timing (in seconds)
% 3.98/1.77  ----------------------
% 3.98/1.77  Preprocessing        : 0.38
% 3.98/1.77  Parsing              : 0.21
% 3.98/1.77  CNF conversion       : 0.03
% 3.98/1.77  Main loop            : 0.53
% 3.98/1.77  Inferencing          : 0.19
% 3.98/1.77  Reduction            : 0.18
% 3.98/1.77  Demodulation         : 0.13
% 3.98/1.77  BG Simplification    : 0.03
% 3.98/1.77  Subsumption          : 0.09
% 3.98/1.77  Abstraction          : 0.03
% 3.98/1.77  MUC search           : 0.00
% 3.98/1.77  Cooper               : 0.00
% 3.98/1.77  Total                : 0.98
% 3.98/1.77  Index Insertion      : 0.00
% 3.98/1.77  Index Deletion       : 0.00
% 3.98/1.77  Index Matching       : 0.00
% 3.98/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
