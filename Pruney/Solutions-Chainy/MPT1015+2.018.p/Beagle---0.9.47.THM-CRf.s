%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:40 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 282 expanded)
%              Number of leaves         :   40 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :  185 ( 881 expanded)
%              Number of equality atoms :   39 (  89 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_144,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_116,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_114,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_111,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_117,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_74])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_102,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_110,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_102])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_77,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_74])).

tff(c_83,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_77])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_56,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_132,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_139,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_132])).

tff(c_215,plain,(
    ! [A_77,B_78] :
      ( k1_relset_1(A_77,A_77,B_78) = A_77
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_zfmisc_1(A_77,A_77)))
      | ~ v1_funct_2(B_78,A_77,A_77)
      | ~ v1_funct_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_218,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_215])).

tff(c_224,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_139,c_218])).

tff(c_16,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_relat_1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_59,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_partfun1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_375,plain,(
    ! [E_111,A_109,B_108,D_107,F_110,C_112] :
      ( m1_subset_1(k1_partfun1(A_109,B_108,C_112,D_107,E_111,F_110),k1_zfmisc_1(k2_zfmisc_1(A_109,D_107)))
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_112,D_107)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_1(E_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_246,plain,(
    ! [D_79,C_80,A_81,B_82] :
      ( D_79 = C_80
      | ~ r2_relset_1(A_81,B_82,C_80,D_79)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_252,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_263,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_252])).

tff(c_264,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_391,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_375,c_264])).

tff(c_421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_58,c_54,c_391])).

tff(c_422,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_512,plain,(
    ! [B_133,F_129,C_130,A_128,D_132,E_131] :
      ( k1_partfun1(A_128,B_133,C_130,D_132,E_131,F_129) = k5_relat_1(E_131,F_129)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_130,D_132)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_128,B_133)))
      | ~ v1_funct_1(E_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_514,plain,(
    ! [A_128,B_133,E_131] :
      ( k1_partfun1(A_128,B_133,'#skF_1','#skF_1',E_131,'#skF_2') = k5_relat_1(E_131,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_128,B_133)))
      | ~ v1_funct_1(E_131) ) ),
    inference(resolution,[status(thm)],[c_54,c_512])).

tff(c_523,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_1','#skF_1',E_136,'#skF_2') = k5_relat_1(E_136,'#skF_2')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_514])).

tff(c_529,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_523])).

tff(c_535,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_422,c_529])).

tff(c_10,plain,(
    ! [A_8,B_12,C_14] :
      ( k5_relat_1(k5_relat_1(A_8,B_12),C_14) = k5_relat_1(A_8,k5_relat_1(B_12,C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_539,plain,(
    ! [C_14] :
      ( k5_relat_1('#skF_3',k5_relat_1('#skF_2',C_14)) = k5_relat_1('#skF_2',C_14)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_10])).

tff(c_986,plain,(
    ! [C_157] :
      ( k5_relat_1('#skF_3',k5_relat_1('#skF_2',C_157)) = k5_relat_1('#skF_2',C_157)
      | ~ v1_relat_1(C_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_83,c_539])).

tff(c_1003,plain,
    ( k5_relat_1('#skF_3',k6_partfun1(k1_relat_1('#skF_2'))) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_986])).

tff(c_1015,plain,
    ( k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_3',k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_44,c_224,c_1003])).

tff(c_1254,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1015])).

tff(c_1286,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1254])).

tff(c_1290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_1286])).

tff(c_1291,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_3',k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1015])).

tff(c_1302,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_1')) = k6_partfun1(k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1291,c_59])).

tff(c_1313,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_44,c_224,c_1302])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [B_16,A_15] :
      ( k5_relat_1(B_16,k6_relat_1(A_15)) = B_16
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_118,plain,(
    ! [B_65,A_66] :
      ( k5_relat_1(B_65,k6_partfun1(A_66)) = B_65
      | ~ r1_tarski(k2_relat_1(B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_122,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_1359,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1313,c_122])).

tff(c_1368,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_110,c_1359])).

tff(c_42,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1373,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1368,c_42])).

tff(c_1376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.70  
% 3.92/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.70  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.92/1.70  
% 3.92/1.70  %Foreground sorts:
% 3.92/1.70  
% 3.92/1.70  
% 3.92/1.70  %Background operators:
% 3.92/1.70  
% 3.92/1.70  
% 3.92/1.70  %Foreground operators:
% 3.92/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.92/1.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.92/1.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.92/1.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.92/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.92/1.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.92/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.92/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.92/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.92/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.92/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.92/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.92/1.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.92/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.92/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.70  
% 3.92/1.72  tff(f_144, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 3.92/1.72  tff(f_92, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.92/1.72  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.92/1.72  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.92/1.72  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.92/1.72  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.92/1.72  tff(f_124, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 3.92/1.72  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.92/1.72  tff(f_116, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.92/1.72  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.92/1.72  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.92/1.72  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.92/1.72  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.92/1.72  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.92/1.72  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.92/1.72  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.92/1.72  tff(c_111, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.92/1.72  tff(c_117, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_111])).
% 3.92/1.72  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.92/1.72  tff(c_74, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_80, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_74])).
% 3.92/1.72  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_80])).
% 3.92/1.72  tff(c_102, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.92/1.72  tff(c_110, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_102])).
% 3.92/1.72  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.92/1.72  tff(c_77, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_54, c_74])).
% 3.92/1.72  tff(c_83, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_77])).
% 3.92/1.72  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.92/1.72  tff(c_44, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.92/1.72  tff(c_56, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.92/1.72  tff(c_132, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.92/1.72  tff(c_139, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_132])).
% 3.92/1.72  tff(c_215, plain, (![A_77, B_78]: (k1_relset_1(A_77, A_77, B_78)=A_77 | ~m1_subset_1(B_78, k1_zfmisc_1(k2_zfmisc_1(A_77, A_77))) | ~v1_funct_2(B_78, A_77, A_77) | ~v1_funct_1(B_78))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.92/1.72  tff(c_218, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_215])).
% 3.92/1.72  tff(c_224, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_139, c_218])).
% 3.92/1.72  tff(c_16, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.72  tff(c_38, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.92/1.72  tff(c_20, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_relat_1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.92/1.72  tff(c_59, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_partfun1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 3.92/1.72  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.92/1.72  tff(c_375, plain, (![E_111, A_109, B_108, D_107, F_110, C_112]: (m1_subset_1(k1_partfun1(A_109, B_108, C_112, D_107, E_111, F_110), k1_zfmisc_1(k2_zfmisc_1(A_109, D_107))) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_112, D_107))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_1(E_111))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.92/1.72  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.92/1.72  tff(c_246, plain, (![D_79, C_80, A_81, B_82]: (D_79=C_80 | ~r2_relset_1(A_81, B_82, C_80, D_79) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.92/1.72  tff(c_252, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_246])).
% 3.92/1.72  tff(c_263, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_252])).
% 3.92/1.72  tff(c_264, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_263])).
% 3.92/1.72  tff(c_391, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_375, c_264])).
% 3.92/1.72  tff(c_421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_58, c_54, c_391])).
% 3.92/1.72  tff(c_422, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_263])).
% 3.92/1.72  tff(c_512, plain, (![B_133, F_129, C_130, A_128, D_132, E_131]: (k1_partfun1(A_128, B_133, C_130, D_132, E_131, F_129)=k5_relat_1(E_131, F_129) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_130, D_132))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_128, B_133))) | ~v1_funct_1(E_131))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.92/1.72  tff(c_514, plain, (![A_128, B_133, E_131]: (k1_partfun1(A_128, B_133, '#skF_1', '#skF_1', E_131, '#skF_2')=k5_relat_1(E_131, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_128, B_133))) | ~v1_funct_1(E_131))), inference(resolution, [status(thm)], [c_54, c_512])).
% 3.92/1.72  tff(c_523, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_1', '#skF_1', E_136, '#skF_2')=k5_relat_1(E_136, '#skF_2') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_514])).
% 3.92/1.72  tff(c_529, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_523])).
% 3.92/1.72  tff(c_535, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_422, c_529])).
% 3.92/1.72  tff(c_10, plain, (![A_8, B_12, C_14]: (k5_relat_1(k5_relat_1(A_8, B_12), C_14)=k5_relat_1(A_8, k5_relat_1(B_12, C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.92/1.72  tff(c_539, plain, (![C_14]: (k5_relat_1('#skF_3', k5_relat_1('#skF_2', C_14))=k5_relat_1('#skF_2', C_14) | ~v1_relat_1(C_14) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_535, c_10])).
% 3.92/1.72  tff(c_986, plain, (![C_157]: (k5_relat_1('#skF_3', k5_relat_1('#skF_2', C_157))=k5_relat_1('#skF_2', C_157) | ~v1_relat_1(C_157))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_83, c_539])).
% 3.92/1.72  tff(c_1003, plain, (k5_relat_1('#skF_3', k6_partfun1(k1_relat_1('#skF_2')))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_59, c_986])).
% 3.92/1.72  tff(c_1015, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_3', k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_44, c_224, c_1003])).
% 3.92/1.72  tff(c_1254, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1015])).
% 3.92/1.72  tff(c_1286, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1254])).
% 3.92/1.72  tff(c_1290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_1286])).
% 3.92/1.72  tff(c_1291, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_3', k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_1015])).
% 3.92/1.72  tff(c_1302, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_1'))=k6_partfun1(k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1291, c_59])).
% 3.92/1.72  tff(c_1313, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_44, c_224, c_1302])).
% 3.92/1.72  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.92/1.72  tff(c_12, plain, (![B_16, A_15]: (k5_relat_1(B_16, k6_relat_1(A_15))=B_16 | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.92/1.72  tff(c_118, plain, (![B_65, A_66]: (k5_relat_1(B_65, k6_partfun1(A_66))=B_65 | ~r1_tarski(k2_relat_1(B_65), A_66) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 3.92/1.72  tff(c_122, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_118])).
% 3.92/1.72  tff(c_1359, plain, (k6_partfun1('#skF_1')='#skF_3' | ~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1313, c_122])).
% 3.92/1.72  tff(c_1368, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_110, c_1359])).
% 3.92/1.72  tff(c_42, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.92/1.72  tff(c_1373, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1368, c_42])).
% 3.92/1.72  tff(c_1376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_1373])).
% 3.92/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.72  
% 3.92/1.72  Inference rules
% 3.92/1.72  ----------------------
% 3.92/1.72  #Ref     : 0
% 3.92/1.72  #Sup     : 298
% 3.92/1.72  #Fact    : 0
% 3.92/1.72  #Define  : 0
% 3.92/1.72  #Split   : 2
% 3.92/1.72  #Chain   : 0
% 3.92/1.72  #Close   : 0
% 3.92/1.72  
% 3.92/1.72  Ordering : KBO
% 3.92/1.72  
% 3.92/1.72  Simplification rules
% 3.92/1.72  ----------------------
% 3.92/1.72  #Subsume      : 0
% 3.92/1.72  #Demod        : 201
% 3.92/1.72  #Tautology    : 76
% 3.92/1.72  #SimpNegUnit  : 0
% 3.92/1.72  #BackRed      : 10
% 3.92/1.72  
% 3.92/1.72  #Partial instantiations: 0
% 3.92/1.72  #Strategies tried      : 1
% 3.92/1.72  
% 3.92/1.72  Timing (in seconds)
% 3.92/1.72  ----------------------
% 3.92/1.72  Preprocessing        : 0.36
% 3.92/1.72  Parsing              : 0.20
% 3.92/1.72  CNF conversion       : 0.02
% 3.92/1.72  Main loop            : 0.54
% 3.92/1.72  Inferencing          : 0.20
% 3.92/1.72  Reduction            : 0.18
% 3.92/1.72  Demodulation         : 0.13
% 3.92/1.72  BG Simplification    : 0.03
% 3.92/1.72  Subsumption          : 0.09
% 3.92/1.72  Abstraction          : 0.03
% 3.92/1.72  MUC search           : 0.00
% 3.92/1.72  Cooper               : 0.00
% 3.92/1.72  Total                : 0.94
% 3.92/1.72  Index Insertion      : 0.00
% 3.92/1.72  Index Deletion       : 0.00
% 3.92/1.72  Index Matching       : 0.00
% 3.92/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
