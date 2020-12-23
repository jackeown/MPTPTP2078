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
% DateTime   : Thu Dec  3 10:15:38 EST 2020

% Result     : Theorem 9.90s
% Output     : CNFRefutation 10.07s
% Verified   : 
% Statistics : Number of formulae       :  193 (4482 expanded)
%              Number of leaves         :   44 (1635 expanded)
%              Depth                    :   17
%              Number of atoms          :  523 (16406 expanded)
%              Number of equality atoms :  106 (1600 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_186,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_144,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_178,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_156,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_138,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_relset_1(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_144,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_138])).

tff(c_96,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_96])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_172,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_180,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_172])).

tff(c_233,plain,(
    ! [A_87,B_88] :
      ( k1_relset_1(A_87,A_87,B_88) = A_87
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k2_zfmisc_1(A_87,A_87)))
      | ~ v1_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_239,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_233])).

tff(c_245,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_180,c_239])).

tff(c_154,plain,(
    ! [A_76] :
      ( k2_relat_1(k2_funct_1(A_76)) = k1_relat_1(A_76)
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [B_67,A_68] :
      ( v5_relat_1(B_67,A_68)
      | ~ r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,(
    ! [B_67] :
      ( v5_relat_1(B_67,k2_relat_1(B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_163,plain,(
    ! [A_76] :
      ( v5_relat_1(k2_funct_1(A_76),k1_relat_1(A_76))
      | ~ v1_relat_1(k2_funct_1(A_76))
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_128])).

tff(c_260,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_163])).

tff(c_264,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_260])).

tff(c_302,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_68,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_58,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_789,plain,(
    ! [B_137,F_134,D_136,E_139,C_138,A_135] :
      ( k1_partfun1(A_135,B_137,C_138,D_136,E_139,F_134) = k5_relat_1(E_139,F_134)
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(C_138,D_136)))
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_135,B_137)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_791,plain,(
    ! [A_135,B_137,E_139] :
      ( k1_partfun1(A_135,B_137,'#skF_1','#skF_1',E_139,'#skF_2') = k5_relat_1(E_139,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_135,B_137)))
      | ~ v1_funct_1(E_139) ) ),
    inference(resolution,[status(thm)],[c_68,c_789])).

tff(c_800,plain,(
    ! [A_140,B_141,E_142] :
      ( k1_partfun1(A_140,B_141,'#skF_1','#skF_1',E_142,'#skF_2') = k5_relat_1(E_142,'#skF_2')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_791])).

tff(c_806,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_800])).

tff(c_812,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_806])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_368,plain,(
    ! [D_98,C_99,A_100,B_101] :
      ( D_98 = C_99
      | ~ r2_relset_1(A_100,B_101,C_99,D_98)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_374,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_368])).

tff(c_385,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_374])).

tff(c_475,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_819,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_475])).

tff(c_843,plain,(
    ! [A_149,B_147,D_151,F_148,E_150,C_146] :
      ( m1_subset_1(k1_partfun1(A_149,B_147,C_146,D_151,E_150,F_148),k1_zfmisc_1(k2_zfmisc_1(A_149,D_151)))
      | ~ m1_subset_1(F_148,k1_zfmisc_1(k2_zfmisc_1(C_146,D_151)))
      | ~ v1_funct_1(F_148)
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(A_149,B_147)))
      | ~ v1_funct_1(E_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_880,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_843])).

tff(c_897,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_72,c_68,c_880])).

tff(c_899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_897])).

tff(c_900,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_1753,plain,(
    ! [C_215,A_217,D_216,B_218,E_214] :
      ( k1_xboole_0 = C_215
      | v2_funct_1(D_216)
      | ~ v2_funct_1(k1_partfun1(A_217,B_218,B_218,C_215,D_216,E_214))
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(B_218,C_215)))
      | ~ v1_funct_2(E_214,B_218,C_215)
      | ~ v1_funct_1(E_214)
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_2(D_216,A_217,B_218)
      | ~ v1_funct_1(D_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1761,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_1753])).

tff(c_1770,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_58,c_1761])).

tff(c_1771,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_1770])).

tff(c_50,plain,(
    ! [D_46,A_43,C_45,E_48] :
      ( v2_funct_1(D_46)
      | ~ v2_funct_1(k1_partfun1(A_43,k1_xboole_0,k1_xboole_0,C_45,D_46,E_48))
      | ~ m1_subset_1(E_48,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,C_45)))
      | ~ v1_funct_2(E_48,k1_xboole_0,C_45)
      | ~ v1_funct_1(E_48)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,k1_xboole_0)))
      | ~ v1_funct_2(D_46,A_43,k1_xboole_0)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4622,plain,(
    ! [D_367,A_368,C_369,E_370] :
      ( v2_funct_1(D_367)
      | ~ v2_funct_1(k1_partfun1(A_368,'#skF_1','#skF_1',C_369,D_367,E_370))
      | ~ m1_subset_1(E_370,k1_zfmisc_1(k2_zfmisc_1('#skF_1',C_369)))
      | ~ v1_funct_2(E_370,'#skF_1',C_369)
      | ~ v1_funct_1(E_370)
      | ~ m1_subset_1(D_367,k1_zfmisc_1(k2_zfmisc_1(A_368,'#skF_1')))
      | ~ v1_funct_2(D_367,A_368,'#skF_1')
      | ~ v1_funct_1(D_367) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1771,c_1771,c_1771,c_1771,c_1771,c_1771,c_50])).

tff(c_4642,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_4622])).

tff(c_4663,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_58,c_4642])).

tff(c_4665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_4663])).

tff(c_4667,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_12,plain,(
    ! [A_5] :
      ( v1_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4666,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_3'))
    | v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_4668,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4666])).

tff(c_4671,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_4668])).

tff(c_4675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_4671])).

tff(c_4677,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4666])).

tff(c_4676,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_4666])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4678,plain,(
    ! [A_371,A_372] :
      ( r1_tarski(k1_relat_1(A_371),A_372)
      | ~ v5_relat_1(k2_funct_1(A_371),A_372)
      | ~ v1_relat_1(k2_funct_1(A_371))
      | ~ v2_funct_1(A_371)
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_10])).

tff(c_4701,plain,(
    ! [A_373] :
      ( r1_tarski(k1_relat_1(A_373),k2_relat_1(k2_funct_1(A_373)))
      | ~ v2_funct_1(A_373)
      | ~ v1_funct_1(A_373)
      | ~ v1_relat_1(A_373)
      | ~ v1_relat_1(k2_funct_1(A_373)) ) ),
    inference(resolution,[status(thm)],[c_128,c_4678])).

tff(c_4709,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_4701])).

tff(c_4722,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4677,c_104,c_66,c_4667,c_4709])).

tff(c_130,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k2_relat_1(B_70),A_71)
      | ~ v5_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [B_70,A_71] :
      ( k2_relat_1(B_70) = A_71
      | ~ r1_tarski(A_71,k2_relat_1(B_70))
      | ~ v5_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_4728,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4722,c_137])).

tff(c_4736,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4677,c_4676,c_4728])).

tff(c_5970,plain,(
    ! [A_464,B_465] :
      ( r1_tarski(k1_relat_1(A_464),k2_relat_1(B_465))
      | ~ v2_funct_1(A_464)
      | k2_relat_1(k5_relat_1(B_465,A_464)) != k2_relat_1(A_464)
      | ~ v1_funct_1(B_465)
      | ~ v1_relat_1(B_465)
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5981,plain,(
    ! [A_464] :
      ( r1_tarski(k1_relat_1(A_464),'#skF_1')
      | ~ v2_funct_1(A_464)
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),A_464)) != k2_relat_1(A_464)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4736,c_5970])).

tff(c_5999,plain,(
    ! [A_464] :
      ( r1_tarski(k1_relat_1(A_464),'#skF_1')
      | ~ v2_funct_1(A_464)
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),A_464)) != k2_relat_1(A_464)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4677,c_5981])).

tff(c_6135,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5999])).

tff(c_6149,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_6135])).

tff(c_6153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_6149])).

tff(c_6155,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5999])).

tff(c_114,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_122,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_5571,plain,(
    ! [C_436,B_435,A_433,D_434,F_432,E_437] :
      ( k1_partfun1(A_433,B_435,C_436,D_434,E_437,F_432) = k5_relat_1(E_437,F_432)
      | ~ m1_subset_1(F_432,k1_zfmisc_1(k2_zfmisc_1(C_436,D_434)))
      | ~ v1_funct_1(F_432)
      | ~ m1_subset_1(E_437,k1_zfmisc_1(k2_zfmisc_1(A_433,B_435)))
      | ~ v1_funct_1(E_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_5573,plain,(
    ! [A_433,B_435,E_437] :
      ( k1_partfun1(A_433,B_435,'#skF_1','#skF_1',E_437,'#skF_2') = k5_relat_1(E_437,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_437,k1_zfmisc_1(k2_zfmisc_1(A_433,B_435)))
      | ~ v1_funct_1(E_437) ) ),
    inference(resolution,[status(thm)],[c_68,c_5571])).

tff(c_5582,plain,(
    ! [A_438,B_439,E_440] :
      ( k1_partfun1(A_438,B_439,'#skF_1','#skF_1',E_440,'#skF_2') = k5_relat_1(E_440,'#skF_2')
      | ~ m1_subset_1(E_440,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439)))
      | ~ v1_funct_1(E_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5573])).

tff(c_5588,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_5582])).

tff(c_5594,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5588])).

tff(c_4785,plain,(
    ! [D_374,C_375,A_376,B_377] :
      ( D_374 = C_375
      | ~ r2_relset_1(A_376,B_377,C_375,D_374)
      | ~ m1_subset_1(D_374,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377)))
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4791,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_4785])).

tff(c_4802,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4791])).

tff(c_4875,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4802])).

tff(c_5601,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5594,c_4875])).

tff(c_5625,plain,(
    ! [F_446,B_445,E_448,A_447,C_444,D_449] :
      ( m1_subset_1(k1_partfun1(A_447,B_445,C_444,D_449,E_448,F_446),k1_zfmisc_1(k2_zfmisc_1(A_447,D_449)))
      | ~ m1_subset_1(F_446,k1_zfmisc_1(k2_zfmisc_1(C_444,D_449)))
      | ~ v1_funct_1(F_446)
      | ~ m1_subset_1(E_448,k1_zfmisc_1(k2_zfmisc_1(A_447,B_445)))
      | ~ v1_funct_1(E_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5662,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5594,c_5625])).

tff(c_5679,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_72,c_68,c_5662])).

tff(c_5681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5601,c_5679])).

tff(c_5682,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4802])).

tff(c_6252,plain,(
    ! [D_497,C_499,A_496,E_500,B_498,F_495] :
      ( k1_partfun1(A_496,B_498,C_499,D_497,E_500,F_495) = k5_relat_1(E_500,F_495)
      | ~ m1_subset_1(F_495,k1_zfmisc_1(k2_zfmisc_1(C_499,D_497)))
      | ~ v1_funct_1(F_495)
      | ~ m1_subset_1(E_500,k1_zfmisc_1(k2_zfmisc_1(A_496,B_498)))
      | ~ v1_funct_1(E_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6254,plain,(
    ! [A_496,B_498,E_500] :
      ( k1_partfun1(A_496,B_498,'#skF_1','#skF_1',E_500,'#skF_2') = k5_relat_1(E_500,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_500,k1_zfmisc_1(k2_zfmisc_1(A_496,B_498)))
      | ~ v1_funct_1(E_500) ) ),
    inference(resolution,[status(thm)],[c_68,c_6252])).

tff(c_6263,plain,(
    ! [A_501,B_502,E_503] :
      ( k1_partfun1(A_501,B_502,'#skF_1','#skF_1',E_503,'#skF_2') = k5_relat_1(E_503,'#skF_2')
      | ~ m1_subset_1(E_503,k1_zfmisc_1(k2_zfmisc_1(A_501,B_502)))
      | ~ v1_funct_1(E_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6254])).

tff(c_6269,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_6263])).

tff(c_6275,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5682,c_6269])).

tff(c_103,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_179,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_172])).

tff(c_236,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_233])).

tff(c_242,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_179,c_236])).

tff(c_5987,plain,(
    ! [B_465] :
      ( r1_tarski('#skF_1',k2_relat_1(B_465))
      | ~ v2_funct_1('#skF_2')
      | k2_relat_1(k5_relat_1(B_465,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_465)
      | ~ v1_relat_1(B_465)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_5970])).

tff(c_6004,plain,(
    ! [B_466] :
      ( r1_tarski('#skF_1',k2_relat_1(B_466))
      | k2_relat_1(k5_relat_1(B_466,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_466)
      | ~ v1_relat_1(B_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_58,c_5987])).

tff(c_6019,plain,(
    ! [B_466] :
      ( k2_relat_1(B_466) = '#skF_1'
      | ~ v5_relat_1(B_466,'#skF_1')
      | k2_relat_1(k5_relat_1(B_466,'#skF_2')) != k2_relat_1('#skF_2')
      | ~ v1_funct_1(B_466)
      | ~ v1_relat_1(B_466) ) ),
    inference(resolution,[status(thm)],[c_6004,c_137])).

tff(c_6279,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6275,c_6019])).

tff(c_6286,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_122,c_6279])).

tff(c_48,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_24,plain,(
    ! [A_13] :
      ( k5_relat_1(k2_funct_1(A_13),A_13) = k6_relat_1(k2_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_74,plain,(
    ! [A_13] :
      ( k5_relat_1(k2_funct_1(A_13),A_13) = k6_partfun1(k2_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_16,plain,(
    ! [B_8,A_6] :
      ( k6_relat_1(k1_relat_1(B_8)) = B_8
      | k5_relat_1(A_6,B_8) != A_6
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5808,plain,(
    ! [B_455,A_456] :
      ( k6_partfun1(k1_relat_1(B_455)) = B_455
      | k5_relat_1(A_456,B_455) != A_456
      | k2_relat_1(A_456) != k1_relat_1(B_455)
      | ~ v1_funct_1(B_455)
      | ~ v1_relat_1(B_455)
      | ~ v1_funct_1(A_456)
      | ~ v1_relat_1(A_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_7187,plain,(
    ! [A_565] :
      ( k6_partfun1(k1_relat_1(A_565)) = A_565
      | k6_partfun1(k2_relat_1(A_565)) != k2_funct_1(A_565)
      | k2_relat_1(k2_funct_1(A_565)) != k1_relat_1(A_565)
      | ~ v1_funct_1(A_565)
      | ~ v1_relat_1(A_565)
      | ~ v1_funct_1(k2_funct_1(A_565))
      | ~ v1_relat_1(k2_funct_1(A_565))
      | ~ v2_funct_1(A_565)
      | ~ v1_funct_1(A_565)
      | ~ v1_relat_1(A_565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_5808])).

tff(c_7190,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k6_partfun1(k2_relat_1('#skF_3')) != k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4677,c_7187])).

tff(c_7199,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | k6_partfun1('#skF_1') != k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_4667,c_6155,c_245,c_4736,c_6286,c_245,c_7190])).

tff(c_7204,plain,(
    k6_partfun1('#skF_1') != k2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7199])).

tff(c_22,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_250,plain,
    ( v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_163])).

tff(c_254,plain,
    ( v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_58,c_250])).

tff(c_274,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_295,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_274])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_295])).

tff(c_301,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_300,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_4712,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_4701])).

tff(c_4724,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_103,c_72,c_58,c_4712])).

tff(c_4805,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4724,c_137])).

tff(c_4813,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_300,c_4805])).

tff(c_5978,plain,(
    ! [A_464] :
      ( r1_tarski(k1_relat_1(A_464),'#skF_1')
      | ~ v2_funct_1(A_464)
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_2'),A_464)) != k2_relat_1(A_464)
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4813,c_5970])).

tff(c_5997,plain,(
    ! [A_464] :
      ( r1_tarski(k1_relat_1(A_464),'#skF_1')
      | ~ v2_funct_1(A_464)
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_2'),A_464)) != k2_relat_1(A_464)
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_5978])).

tff(c_6182,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5997])).

tff(c_6185,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_6182])).

tff(c_6189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_6185])).

tff(c_6191,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5997])).

tff(c_5943,plain,(
    ! [B_462,A_463] :
      ( k5_relat_1(k2_funct_1(B_462),k2_funct_1(A_463)) = k2_funct_1(k5_relat_1(A_463,B_462))
      | ~ v2_funct_1(B_462)
      | ~ v2_funct_1(A_463)
      | ~ v1_funct_1(B_462)
      | ~ v1_relat_1(B_462)
      | ~ v1_funct_1(A_463)
      | ~ v1_relat_1(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_75,plain,(
    ! [B_8,A_6] :
      ( k6_partfun1(k1_relat_1(B_8)) = B_8
      | k5_relat_1(A_6,B_8) != A_6
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_8698,plain,(
    ! [A_621,B_622] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_621))) = k2_funct_1(A_621)
      | k2_funct_1(k5_relat_1(A_621,B_622)) != k2_funct_1(B_622)
      | k2_relat_1(k2_funct_1(B_622)) != k1_relat_1(k2_funct_1(A_621))
      | ~ v1_funct_1(k2_funct_1(A_621))
      | ~ v1_relat_1(k2_funct_1(A_621))
      | ~ v1_funct_1(k2_funct_1(B_622))
      | ~ v1_relat_1(k2_funct_1(B_622))
      | ~ v2_funct_1(B_622)
      | ~ v2_funct_1(A_621)
      | ~ v1_funct_1(B_622)
      | ~ v1_relat_1(B_622)
      | ~ v1_funct_1(A_621)
      | ~ v1_relat_1(A_621) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5943,c_75])).

tff(c_8704,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_2')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6275,c_8698])).

tff(c_8713,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_103,c_72,c_4667,c_58,c_301,c_6191,c_4677,c_6155,c_4813,c_8704])).

tff(c_8714,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8713])).

tff(c_8717,plain,
    ( k2_relat_1('#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8714])).

tff(c_8720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_4667,c_6286,c_8717])).

tff(c_8722,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8713])).

tff(c_8721,plain,(
    k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_8713])).

tff(c_8837,plain,(
    k6_partfun1('#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8722,c_8721])).

tff(c_8838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7204,c_8837])).

tff(c_8839,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7199])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_8841,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8839,c_56])).

tff(c_8844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_8841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:17:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.90/3.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.07/3.54  
% 10.07/3.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.07/3.54  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.07/3.54  
% 10.07/3.54  %Foreground sorts:
% 10.07/3.54  
% 10.07/3.54  
% 10.07/3.54  %Background operators:
% 10.07/3.54  
% 10.07/3.54  
% 10.07/3.54  %Foreground operators:
% 10.07/3.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.07/3.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.07/3.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.07/3.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.07/3.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.07/3.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.07/3.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.07/3.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.07/3.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.07/3.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.07/3.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.07/3.54  tff('#skF_2', type, '#skF_2': $i).
% 10.07/3.54  tff('#skF_3', type, '#skF_3': $i).
% 10.07/3.54  tff('#skF_1', type, '#skF_1': $i).
% 10.07/3.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.07/3.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.07/3.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.07/3.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.07/3.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.07/3.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.07/3.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.07/3.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.07/3.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.07/3.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.07/3.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.07/3.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.07/3.54  
% 10.07/3.57  tff(f_206, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 10.07/3.57  tff(f_132, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.07/3.57  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.07/3.57  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.07/3.57  tff(f_186, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 10.07/3.57  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.07/3.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.07/3.57  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 10.07/3.57  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.07/3.57  tff(f_144, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.07/3.57  tff(f_178, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 10.07/3.57  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.07/3.57  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 10.07/3.57  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.07/3.57  tff(f_156, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.07/3.57  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 10.07/3.57  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 10.07/3.57  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 10.07/3.57  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_138, plain, (![A_72, B_73, D_74]: (r2_relset_1(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.07/3.57  tff(c_144, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_138])).
% 10.07/3.57  tff(c_96, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 10.07/3.57  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_96])).
% 10.07/3.57  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_172, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.07/3.57  tff(c_180, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_172])).
% 10.07/3.57  tff(c_233, plain, (![A_87, B_88]: (k1_relset_1(A_87, A_87, B_88)=A_87 | ~m1_subset_1(B_88, k1_zfmisc_1(k2_zfmisc_1(A_87, A_87))) | ~v1_funct_2(B_88, A_87, A_87) | ~v1_funct_1(B_88))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.07/3.57  tff(c_239, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_233])).
% 10.07/3.57  tff(c_245, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_180, c_239])).
% 10.07/3.57  tff(c_154, plain, (![A_76]: (k2_relat_1(k2_funct_1(A_76))=k1_relat_1(A_76) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.07/3.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.07/3.57  tff(c_123, plain, (![B_67, A_68]: (v5_relat_1(B_67, A_68) | ~r1_tarski(k2_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.07/3.57  tff(c_128, plain, (![B_67]: (v5_relat_1(B_67, k2_relat_1(B_67)) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_6, c_123])).
% 10.07/3.57  tff(c_163, plain, (![A_76]: (v5_relat_1(k2_funct_1(A_76), k1_relat_1(A_76)) | ~v1_relat_1(k2_funct_1(A_76)) | ~v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_154, c_128])).
% 10.07/3.57  tff(c_260, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_245, c_163])).
% 10.07/3.57  tff(c_264, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_260])).
% 10.07/3.57  tff(c_302, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_264])).
% 10.07/3.57  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_58, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_789, plain, (![B_137, F_134, D_136, E_139, C_138, A_135]: (k1_partfun1(A_135, B_137, C_138, D_136, E_139, F_134)=k5_relat_1(E_139, F_134) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(C_138, D_136))) | ~v1_funct_1(F_134) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_135, B_137))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.07/3.57  tff(c_791, plain, (![A_135, B_137, E_139]: (k1_partfun1(A_135, B_137, '#skF_1', '#skF_1', E_139, '#skF_2')=k5_relat_1(E_139, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_135, B_137))) | ~v1_funct_1(E_139))), inference(resolution, [status(thm)], [c_68, c_789])).
% 10.07/3.57  tff(c_800, plain, (![A_140, B_141, E_142]: (k1_partfun1(A_140, B_141, '#skF_1', '#skF_1', E_142, '#skF_2')=k5_relat_1(E_142, '#skF_2') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_1(E_142))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_791])).
% 10.07/3.57  tff(c_806, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_800])).
% 10.07/3.57  tff(c_812, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_806])).
% 10.07/3.57  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_368, plain, (![D_98, C_99, A_100, B_101]: (D_98=C_99 | ~r2_relset_1(A_100, B_101, C_99, D_98) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.07/3.57  tff(c_374, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_368])).
% 10.07/3.57  tff(c_385, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_374])).
% 10.07/3.57  tff(c_475, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_385])).
% 10.07/3.57  tff(c_819, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_812, c_475])).
% 10.07/3.57  tff(c_843, plain, (![A_149, B_147, D_151, F_148, E_150, C_146]: (m1_subset_1(k1_partfun1(A_149, B_147, C_146, D_151, E_150, F_148), k1_zfmisc_1(k2_zfmisc_1(A_149, D_151))) | ~m1_subset_1(F_148, k1_zfmisc_1(k2_zfmisc_1(C_146, D_151))) | ~v1_funct_1(F_148) | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(A_149, B_147))) | ~v1_funct_1(E_150))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.07/3.57  tff(c_880, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_812, c_843])).
% 10.07/3.57  tff(c_897, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_72, c_68, c_880])).
% 10.07/3.57  tff(c_899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_819, c_897])).
% 10.07/3.57  tff(c_900, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_385])).
% 10.07/3.57  tff(c_1753, plain, (![C_215, A_217, D_216, B_218, E_214]: (k1_xboole_0=C_215 | v2_funct_1(D_216) | ~v2_funct_1(k1_partfun1(A_217, B_218, B_218, C_215, D_216, E_214)) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(B_218, C_215))) | ~v1_funct_2(E_214, B_218, C_215) | ~v1_funct_1(E_214) | ~m1_subset_1(D_216, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_2(D_216, A_217, B_218) | ~v1_funct_1(D_216))), inference(cnfTransformation, [status(thm)], [f_178])).
% 10.07/3.57  tff(c_1761, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1('#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_900, c_1753])).
% 10.07/3.57  tff(c_1770, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_58, c_1761])).
% 10.07/3.57  tff(c_1771, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_302, c_1770])).
% 10.07/3.57  tff(c_50, plain, (![D_46, A_43, C_45, E_48]: (v2_funct_1(D_46) | ~v2_funct_1(k1_partfun1(A_43, k1_xboole_0, k1_xboole_0, C_45, D_46, E_48)) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, C_45))) | ~v1_funct_2(E_48, k1_xboole_0, C_45) | ~v1_funct_1(E_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, k1_xboole_0))) | ~v1_funct_2(D_46, A_43, k1_xboole_0) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_178])).
% 10.07/3.57  tff(c_4622, plain, (![D_367, A_368, C_369, E_370]: (v2_funct_1(D_367) | ~v2_funct_1(k1_partfun1(A_368, '#skF_1', '#skF_1', C_369, D_367, E_370)) | ~m1_subset_1(E_370, k1_zfmisc_1(k2_zfmisc_1('#skF_1', C_369))) | ~v1_funct_2(E_370, '#skF_1', C_369) | ~v1_funct_1(E_370) | ~m1_subset_1(D_367, k1_zfmisc_1(k2_zfmisc_1(A_368, '#skF_1'))) | ~v1_funct_2(D_367, A_368, '#skF_1') | ~v1_funct_1(D_367))), inference(demodulation, [status(thm), theory('equality')], [c_1771, c_1771, c_1771, c_1771, c_1771, c_1771, c_50])).
% 10.07/3.57  tff(c_4642, plain, (v2_funct_1('#skF_3') | ~v2_funct_1('#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_900, c_4622])).
% 10.07/3.57  tff(c_4663, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_58, c_4642])).
% 10.07/3.57  tff(c_4665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_302, c_4663])).
% 10.07/3.57  tff(c_4667, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_264])).
% 10.07/3.57  tff(c_12, plain, (![A_5]: (v1_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.07/3.57  tff(c_14, plain, (![A_5]: (v1_relat_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.07/3.57  tff(c_4666, plain, (~v1_relat_1(k2_funct_1('#skF_3')) | v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_264])).
% 10.07/3.57  tff(c_4668, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4666])).
% 10.07/3.57  tff(c_4671, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_4668])).
% 10.07/3.57  tff(c_4675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_4671])).
% 10.07/3.57  tff(c_4677, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4666])).
% 10.07/3.57  tff(c_4676, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_4666])).
% 10.07/3.57  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.07/3.57  tff(c_4678, plain, (![A_371, A_372]: (r1_tarski(k1_relat_1(A_371), A_372) | ~v5_relat_1(k2_funct_1(A_371), A_372) | ~v1_relat_1(k2_funct_1(A_371)) | ~v2_funct_1(A_371) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(superposition, [status(thm), theory('equality')], [c_154, c_10])).
% 10.07/3.57  tff(c_4701, plain, (![A_373]: (r1_tarski(k1_relat_1(A_373), k2_relat_1(k2_funct_1(A_373))) | ~v2_funct_1(A_373) | ~v1_funct_1(A_373) | ~v1_relat_1(A_373) | ~v1_relat_1(k2_funct_1(A_373)))), inference(resolution, [status(thm)], [c_128, c_4678])).
% 10.07/3.57  tff(c_4709, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_245, c_4701])).
% 10.07/3.57  tff(c_4722, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4677, c_104, c_66, c_4667, c_4709])).
% 10.07/3.57  tff(c_130, plain, (![B_70, A_71]: (r1_tarski(k2_relat_1(B_70), A_71) | ~v5_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.07/3.57  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.07/3.57  tff(c_137, plain, (![B_70, A_71]: (k2_relat_1(B_70)=A_71 | ~r1_tarski(A_71, k2_relat_1(B_70)) | ~v5_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_130, c_2])).
% 10.07/3.57  tff(c_4728, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4722, c_137])).
% 10.07/3.57  tff(c_4736, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4677, c_4676, c_4728])).
% 10.07/3.57  tff(c_5970, plain, (![A_464, B_465]: (r1_tarski(k1_relat_1(A_464), k2_relat_1(B_465)) | ~v2_funct_1(A_464) | k2_relat_1(k5_relat_1(B_465, A_464))!=k2_relat_1(A_464) | ~v1_funct_1(B_465) | ~v1_relat_1(B_465) | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.07/3.57  tff(c_5981, plain, (![A_464]: (r1_tarski(k1_relat_1(A_464), '#skF_1') | ~v2_funct_1(A_464) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), A_464))!=k2_relat_1(A_464) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(superposition, [status(thm), theory('equality')], [c_4736, c_5970])).
% 10.07/3.57  tff(c_5999, plain, (![A_464]: (r1_tarski(k1_relat_1(A_464), '#skF_1') | ~v2_funct_1(A_464) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), A_464))!=k2_relat_1(A_464) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(demodulation, [status(thm), theory('equality')], [c_4677, c_5981])).
% 10.07/3.57  tff(c_6135, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5999])).
% 10.07/3.57  tff(c_6149, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_6135])).
% 10.07/3.57  tff(c_6153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_6149])).
% 10.07/3.57  tff(c_6155, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5999])).
% 10.07/3.57  tff(c_114, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.07/3.57  tff(c_122, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_114])).
% 10.07/3.57  tff(c_5571, plain, (![C_436, B_435, A_433, D_434, F_432, E_437]: (k1_partfun1(A_433, B_435, C_436, D_434, E_437, F_432)=k5_relat_1(E_437, F_432) | ~m1_subset_1(F_432, k1_zfmisc_1(k2_zfmisc_1(C_436, D_434))) | ~v1_funct_1(F_432) | ~m1_subset_1(E_437, k1_zfmisc_1(k2_zfmisc_1(A_433, B_435))) | ~v1_funct_1(E_437))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.07/3.57  tff(c_5573, plain, (![A_433, B_435, E_437]: (k1_partfun1(A_433, B_435, '#skF_1', '#skF_1', E_437, '#skF_2')=k5_relat_1(E_437, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_437, k1_zfmisc_1(k2_zfmisc_1(A_433, B_435))) | ~v1_funct_1(E_437))), inference(resolution, [status(thm)], [c_68, c_5571])).
% 10.07/3.57  tff(c_5582, plain, (![A_438, B_439, E_440]: (k1_partfun1(A_438, B_439, '#skF_1', '#skF_1', E_440, '#skF_2')=k5_relat_1(E_440, '#skF_2') | ~m1_subset_1(E_440, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))) | ~v1_funct_1(E_440))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5573])).
% 10.07/3.57  tff(c_5588, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_5582])).
% 10.07/3.57  tff(c_5594, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5588])).
% 10.07/3.57  tff(c_4785, plain, (![D_374, C_375, A_376, B_377]: (D_374=C_375 | ~r2_relset_1(A_376, B_377, C_375, D_374) | ~m1_subset_1(D_374, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.07/3.57  tff(c_4791, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_4785])).
% 10.07/3.57  tff(c_4802, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4791])).
% 10.07/3.57  tff(c_4875, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4802])).
% 10.07/3.57  tff(c_5601, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5594, c_4875])).
% 10.07/3.57  tff(c_5625, plain, (![F_446, B_445, E_448, A_447, C_444, D_449]: (m1_subset_1(k1_partfun1(A_447, B_445, C_444, D_449, E_448, F_446), k1_zfmisc_1(k2_zfmisc_1(A_447, D_449))) | ~m1_subset_1(F_446, k1_zfmisc_1(k2_zfmisc_1(C_444, D_449))) | ~v1_funct_1(F_446) | ~m1_subset_1(E_448, k1_zfmisc_1(k2_zfmisc_1(A_447, B_445))) | ~v1_funct_1(E_448))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.07/3.57  tff(c_5662, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5594, c_5625])).
% 10.07/3.57  tff(c_5679, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_72, c_68, c_5662])).
% 10.07/3.57  tff(c_5681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5601, c_5679])).
% 10.07/3.57  tff(c_5682, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_4802])).
% 10.07/3.57  tff(c_6252, plain, (![D_497, C_499, A_496, E_500, B_498, F_495]: (k1_partfun1(A_496, B_498, C_499, D_497, E_500, F_495)=k5_relat_1(E_500, F_495) | ~m1_subset_1(F_495, k1_zfmisc_1(k2_zfmisc_1(C_499, D_497))) | ~v1_funct_1(F_495) | ~m1_subset_1(E_500, k1_zfmisc_1(k2_zfmisc_1(A_496, B_498))) | ~v1_funct_1(E_500))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.07/3.57  tff(c_6254, plain, (![A_496, B_498, E_500]: (k1_partfun1(A_496, B_498, '#skF_1', '#skF_1', E_500, '#skF_2')=k5_relat_1(E_500, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_500, k1_zfmisc_1(k2_zfmisc_1(A_496, B_498))) | ~v1_funct_1(E_500))), inference(resolution, [status(thm)], [c_68, c_6252])).
% 10.07/3.57  tff(c_6263, plain, (![A_501, B_502, E_503]: (k1_partfun1(A_501, B_502, '#skF_1', '#skF_1', E_503, '#skF_2')=k5_relat_1(E_503, '#skF_2') | ~m1_subset_1(E_503, k1_zfmisc_1(k2_zfmisc_1(A_501, B_502))) | ~v1_funct_1(E_503))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6254])).
% 10.07/3.57  tff(c_6269, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_6263])).
% 10.07/3.57  tff(c_6275, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5682, c_6269])).
% 10.07/3.57  tff(c_103, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_96])).
% 10.07/3.57  tff(c_179, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_172])).
% 10.07/3.57  tff(c_236, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_233])).
% 10.07/3.57  tff(c_242, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_179, c_236])).
% 10.07/3.57  tff(c_5987, plain, (![B_465]: (r1_tarski('#skF_1', k2_relat_1(B_465)) | ~v2_funct_1('#skF_2') | k2_relat_1(k5_relat_1(B_465, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_465) | ~v1_relat_1(B_465) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_5970])).
% 10.07/3.57  tff(c_6004, plain, (![B_466]: (r1_tarski('#skF_1', k2_relat_1(B_466)) | k2_relat_1(k5_relat_1(B_466, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_466) | ~v1_relat_1(B_466))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_58, c_5987])).
% 10.07/3.57  tff(c_6019, plain, (![B_466]: (k2_relat_1(B_466)='#skF_1' | ~v5_relat_1(B_466, '#skF_1') | k2_relat_1(k5_relat_1(B_466, '#skF_2'))!=k2_relat_1('#skF_2') | ~v1_funct_1(B_466) | ~v1_relat_1(B_466))), inference(resolution, [status(thm)], [c_6004, c_137])).
% 10.07/3.57  tff(c_6279, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v5_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6275, c_6019])).
% 10.07/3.57  tff(c_6286, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_122, c_6279])).
% 10.07/3.57  tff(c_48, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.07/3.57  tff(c_24, plain, (![A_13]: (k5_relat_1(k2_funct_1(A_13), A_13)=k6_relat_1(k2_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.07/3.57  tff(c_74, plain, (![A_13]: (k5_relat_1(k2_funct_1(A_13), A_13)=k6_partfun1(k2_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 10.07/3.57  tff(c_16, plain, (![B_8, A_6]: (k6_relat_1(k1_relat_1(B_8))=B_8 | k5_relat_1(A_6, B_8)!=A_6 | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.07/3.57  tff(c_5808, plain, (![B_455, A_456]: (k6_partfun1(k1_relat_1(B_455))=B_455 | k5_relat_1(A_456, B_455)!=A_456 | k2_relat_1(A_456)!=k1_relat_1(B_455) | ~v1_funct_1(B_455) | ~v1_relat_1(B_455) | ~v1_funct_1(A_456) | ~v1_relat_1(A_456))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 10.07/3.57  tff(c_7187, plain, (![A_565]: (k6_partfun1(k1_relat_1(A_565))=A_565 | k6_partfun1(k2_relat_1(A_565))!=k2_funct_1(A_565) | k2_relat_1(k2_funct_1(A_565))!=k1_relat_1(A_565) | ~v1_funct_1(A_565) | ~v1_relat_1(A_565) | ~v1_funct_1(k2_funct_1(A_565)) | ~v1_relat_1(k2_funct_1(A_565)) | ~v2_funct_1(A_565) | ~v1_funct_1(A_565) | ~v1_relat_1(A_565))), inference(superposition, [status(thm), theory('equality')], [c_74, c_5808])).
% 10.07/3.57  tff(c_7190, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k6_partfun1(k2_relat_1('#skF_3'))!=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4677, c_7187])).
% 10.07/3.57  tff(c_7199, plain, (k6_partfun1('#skF_1')='#skF_3' | k6_partfun1('#skF_1')!=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_4667, c_6155, c_245, c_4736, c_6286, c_245, c_7190])).
% 10.07/3.57  tff(c_7204, plain, (k6_partfun1('#skF_1')!=k2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_7199])).
% 10.07/3.57  tff(c_22, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.07/3.57  tff(c_250, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_242, c_163])).
% 10.07/3.57  tff(c_254, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_58, c_250])).
% 10.07/3.57  tff(c_274, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_254])).
% 10.07/3.57  tff(c_295, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_274])).
% 10.07/3.57  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_295])).
% 10.07/3.57  tff(c_301, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_254])).
% 10.07/3.57  tff(c_300, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_254])).
% 10.07/3.57  tff(c_4712, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_4701])).
% 10.07/3.57  tff(c_4724, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_103, c_72, c_58, c_4712])).
% 10.07/3.57  tff(c_4805, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_4724, c_137])).
% 10.07/3.57  tff(c_4813, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_300, c_4805])).
% 10.07/3.57  tff(c_5978, plain, (![A_464]: (r1_tarski(k1_relat_1(A_464), '#skF_1') | ~v2_funct_1(A_464) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_2'), A_464))!=k2_relat_1(A_464) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(superposition, [status(thm), theory('equality')], [c_4813, c_5970])).
% 10.07/3.57  tff(c_5997, plain, (![A_464]: (r1_tarski(k1_relat_1(A_464), '#skF_1') | ~v2_funct_1(A_464) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_2'), A_464))!=k2_relat_1(A_464) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_5978])).
% 10.07/3.57  tff(c_6182, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_5997])).
% 10.07/3.57  tff(c_6185, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_6182])).
% 10.07/3.57  tff(c_6189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_6185])).
% 10.07/3.57  tff(c_6191, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_5997])).
% 10.07/3.57  tff(c_5943, plain, (![B_462, A_463]: (k5_relat_1(k2_funct_1(B_462), k2_funct_1(A_463))=k2_funct_1(k5_relat_1(A_463, B_462)) | ~v2_funct_1(B_462) | ~v2_funct_1(A_463) | ~v1_funct_1(B_462) | ~v1_relat_1(B_462) | ~v1_funct_1(A_463) | ~v1_relat_1(A_463))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.07/3.57  tff(c_75, plain, (![B_8, A_6]: (k6_partfun1(k1_relat_1(B_8))=B_8 | k5_relat_1(A_6, B_8)!=A_6 | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 10.07/3.57  tff(c_8698, plain, (![A_621, B_622]: (k6_partfun1(k1_relat_1(k2_funct_1(A_621)))=k2_funct_1(A_621) | k2_funct_1(k5_relat_1(A_621, B_622))!=k2_funct_1(B_622) | k2_relat_1(k2_funct_1(B_622))!=k1_relat_1(k2_funct_1(A_621)) | ~v1_funct_1(k2_funct_1(A_621)) | ~v1_relat_1(k2_funct_1(A_621)) | ~v1_funct_1(k2_funct_1(B_622)) | ~v1_relat_1(k2_funct_1(B_622)) | ~v2_funct_1(B_622) | ~v2_funct_1(A_621) | ~v1_funct_1(B_622) | ~v1_relat_1(B_622) | ~v1_funct_1(A_621) | ~v1_relat_1(A_621))), inference(superposition, [status(thm), theory('equality')], [c_5943, c_75])).
% 10.07/3.57  tff(c_8704, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6275, c_8698])).
% 10.07/3.57  tff(c_8713, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_103, c_72, c_4667, c_58, c_301, c_6191, c_4677, c_6155, c_4813, c_8704])).
% 10.07/3.57  tff(c_8714, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_8713])).
% 10.07/3.57  tff(c_8717, plain, (k2_relat_1('#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_8714])).
% 10.07/3.57  tff(c_8720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_4667, c_6286, c_8717])).
% 10.07/3.57  tff(c_8722, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_8713])).
% 10.07/3.57  tff(c_8721, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_8713])).
% 10.07/3.57  tff(c_8837, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8722, c_8721])).
% 10.07/3.57  tff(c_8838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7204, c_8837])).
% 10.07/3.57  tff(c_8839, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_7199])).
% 10.07/3.57  tff(c_56, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.07/3.57  tff(c_8841, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8839, c_56])).
% 10.07/3.57  tff(c_8844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_8841])).
% 10.07/3.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.07/3.57  
% 10.07/3.57  Inference rules
% 10.07/3.57  ----------------------
% 10.07/3.57  #Ref     : 0
% 10.07/3.57  #Sup     : 1807
% 10.07/3.57  #Fact    : 0
% 10.07/3.57  #Define  : 0
% 10.07/3.57  #Split   : 27
% 10.07/3.57  #Chain   : 0
% 10.07/3.57  #Close   : 0
% 10.07/3.57  
% 10.07/3.57  Ordering : KBO
% 10.07/3.57  
% 10.07/3.57  Simplification rules
% 10.07/3.57  ----------------------
% 10.07/3.57  #Subsume      : 138
% 10.07/3.57  #Demod        : 3259
% 10.07/3.57  #Tautology    : 536
% 10.07/3.57  #SimpNegUnit  : 8
% 10.07/3.57  #BackRed      : 67
% 10.07/3.57  
% 10.07/3.57  #Partial instantiations: 0
% 10.07/3.57  #Strategies tried      : 1
% 10.07/3.57  
% 10.07/3.57  Timing (in seconds)
% 10.07/3.57  ----------------------
% 10.07/3.57  Preprocessing        : 0.40
% 10.07/3.57  Parsing              : 0.22
% 10.07/3.57  CNF conversion       : 0.03
% 10.07/3.57  Main loop            : 2.38
% 10.07/3.57  Inferencing          : 0.74
% 10.07/3.57  Reduction            : 0.99
% 10.07/3.57  Demodulation         : 0.77
% 10.07/3.57  BG Simplification    : 0.07
% 10.07/3.57  Subsumption          : 0.45
% 10.07/3.57  Abstraction          : 0.08
% 10.07/3.57  MUC search           : 0.00
% 10.07/3.57  Cooper               : 0.00
% 10.07/3.57  Total                : 2.85
% 10.07/3.57  Index Insertion      : 0.00
% 10.07/3.57  Index Deletion       : 0.00
% 10.07/3.57  Index Matching       : 0.00
% 10.07/3.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
