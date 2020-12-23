%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:24 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :  172 (1223 expanded)
%              Number of leaves         :   41 ( 443 expanded)
%              Depth                    :   23
%              Number of atoms          :  431 (4919 expanded)
%              Number of equality atoms :  162 (1698 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_194,negated_conjecture,(
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

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_109,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
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

tff(f_168,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_126,axiom,(
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

tff(f_152,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_338,plain,(
    ! [C_103,E_104,D_99,F_102,A_101,B_100] :
      ( k1_partfun1(A_101,B_100,C_103,D_99,E_104,F_102) = k5_relat_1(E_104,F_102)
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(C_103,D_99)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_1(E_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_342,plain,(
    ! [A_101,B_100,E_104] :
      ( k1_partfun1(A_101,B_100,'#skF_2','#skF_1',E_104,'#skF_4') = k5_relat_1(E_104,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_1(E_104) ) ),
    inference(resolution,[status(thm)],[c_64,c_338])).

tff(c_421,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,'#skF_2','#skF_1',E_118,'#skF_4') = k5_relat_1(E_118,'#skF_4')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_342])).

tff(c_430,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_421])).

tff(c_437,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_430])).

tff(c_32,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_198,plain,(
    ! [D_69,C_70,A_71,B_72] :
      ( D_69 = C_70
      | ~ r2_relset_1(A_71,B_72,C_70,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_206,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_198])).

tff(c_221,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_206])).

tff(c_222,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_444,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_222])).

tff(c_571,plain,(
    ! [D_127,C_122,E_123,B_124,F_126,A_125] :
      ( m1_subset_1(k1_partfun1(A_125,B_124,C_122,D_127,E_123,F_126),k1_zfmisc_1(k2_zfmisc_1(A_125,D_127)))
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_122,D_127)))
      | ~ v1_funct_1(F_126)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_1(E_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_604,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_571])).

tff(c_629,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_604])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_629])).

tff(c_632,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_683,plain,(
    ! [C_132,D_137,E_133,B_134,F_136,A_135] :
      ( v1_funct_1(k1_partfun1(A_135,B_134,C_132,D_137,E_133,F_136))
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_132,D_137)))
      | ~ v1_funct_1(F_136)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_687,plain,(
    ! [A_135,B_134,E_133] :
      ( v1_funct_1(k1_partfun1(A_135,B_134,'#skF_2','#skF_1',E_133,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134)))
      | ~ v1_funct_1(E_133) ) ),
    inference(resolution,[status(thm)],[c_64,c_683])).

tff(c_697,plain,(
    ! [A_138,B_139,E_140] :
      ( v1_funct_1(k1_partfun1(A_138,B_139,'#skF_2','#skF_1',E_140,'#skF_4'))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_687])).

tff(c_706,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_697])).

tff(c_713,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_632,c_706])).

tff(c_36,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_10,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_79,plain,(
    ! [A_7] : v1_relat_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_118,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_118])).

tff(c_136,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_127])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_147,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_156,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_147])).

tff(c_161,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_156])).

tff(c_18,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_relat_1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_641,plain,(
    ! [A_128,B_129] :
      ( k2_funct_1(A_128) = B_129
      | k6_partfun1(k2_relat_1(A_128)) != k5_relat_1(B_129,A_128)
      | k2_relat_1(B_129) != k1_relat_1(A_128)
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_647,plain,(
    ! [B_129] :
      ( k2_funct_1('#skF_3') = B_129
      | k5_relat_1(B_129,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_129) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_641])).

tff(c_656,plain,(
    ! [B_130] :
      ( k2_funct_1('#skF_3') = B_130
      | k5_relat_1(B_130,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_130) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74,c_58,c_647])).

tff(c_668,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_7)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_79,c_656])).

tff(c_678,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_7
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_668])).

tff(c_717,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_713,c_678])).

tff(c_737,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_717])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_792,plain,(
    ! [A_156,C_157,B_158] :
      ( k6_partfun1(A_156) = k5_relat_1(C_157,k2_funct_1(C_157))
      | k1_xboole_0 = B_158
      | ~ v2_funct_1(C_157)
      | k2_relset_1(A_156,B_158,C_157) != B_158
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_158)))
      | ~ v1_funct_2(C_157,A_156,B_158)
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_798,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_792])).

tff(c_808,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_798])).

tff(c_809,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_808])).

tff(c_16,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_partfun1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_813,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_76])).

tff(c_820,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74,c_58,c_813])).

tff(c_853,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_80])).

tff(c_874,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_853])).

tff(c_876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_737,c_874])).

tff(c_878,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_717])).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_124,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_118])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_124])).

tff(c_662,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_656])).

tff(c_674,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_662])).

tff(c_675,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_674])).

tff(c_679,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_675])).

tff(c_881,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_679])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_137,plain,(
    ! [A_59,B_60,D_61] :
      ( r2_relset_1(A_59,B_60,D_61,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_144,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_32,c_137])).

tff(c_159,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_147])).

tff(c_1706,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( k2_relset_1(A_223,B_224,C_225) = B_224
      | ~ r2_relset_1(B_224,B_224,k1_partfun1(B_224,A_223,A_223,B_224,D_226,C_225),k6_partfun1(B_224))
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1(B_224,A_223)))
      | ~ v1_funct_2(D_226,B_224,A_223)
      | ~ v1_funct_1(D_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_2(C_225,A_223,B_224)
      | ~ v1_funct_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1712,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_1706])).

tff(c_1716,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_144,c_159,c_1712])).

tff(c_1718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_881,c_1716])).

tff(c_1719,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_675])).

tff(c_2857,plain,(
    ! [C_345,F_344,A_343,E_346,D_341,B_342] :
      ( k1_partfun1(A_343,B_342,C_345,D_341,E_346,F_344) = k5_relat_1(E_346,F_344)
      | ~ m1_subset_1(F_344,k1_zfmisc_1(k2_zfmisc_1(C_345,D_341)))
      | ~ v1_funct_1(F_344)
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_343,B_342)))
      | ~ v1_funct_1(E_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2861,plain,(
    ! [A_343,B_342,E_346] :
      ( k1_partfun1(A_343,B_342,'#skF_2','#skF_1',E_346,'#skF_4') = k5_relat_1(E_346,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_343,B_342)))
      | ~ v1_funct_1(E_346) ) ),
    inference(resolution,[status(thm)],[c_64,c_2857])).

tff(c_3297,plain,(
    ! [A_376,B_377,E_378] :
      ( k1_partfun1(A_376,B_377,'#skF_2','#skF_1',E_378,'#skF_4') = k5_relat_1(E_378,'#skF_4')
      | ~ m1_subset_1(E_378,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377)))
      | ~ v1_funct_1(E_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2861])).

tff(c_3306,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_3297])).

tff(c_3313,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_632,c_3306])).

tff(c_1720,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_675])).

tff(c_75,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_partfun1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_1724,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1720,c_75])).

tff(c_1728,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_68,c_1724])).

tff(c_1736,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1728])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12])).

tff(c_2787,plain,(
    ! [C_323,D_324,B_322,E_325,A_321] :
      ( k1_xboole_0 = C_323
      | v2_funct_1(E_325)
      | k2_relset_1(A_321,B_322,D_324) != B_322
      | ~ v2_funct_1(k1_partfun1(A_321,B_322,B_322,C_323,D_324,E_325))
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(B_322,C_323)))
      | ~ v1_funct_2(E_325,B_322,C_323)
      | ~ v1_funct_1(E_325)
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322)))
      | ~ v1_funct_2(D_324,A_321,B_322)
      | ~ v1_funct_1(D_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2793,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_2787])).

tff(c_2801,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_78,c_62,c_2793])).

tff(c_2803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1736,c_56,c_2801])).

tff(c_2805,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1728])).

tff(c_2821,plain,(
    ! [C_331,B_333,F_335,D_336,A_334,E_332] :
      ( v1_funct_1(k1_partfun1(A_334,B_333,C_331,D_336,E_332,F_335))
      | ~ m1_subset_1(F_335,k1_zfmisc_1(k2_zfmisc_1(C_331,D_336)))
      | ~ v1_funct_1(F_335)
      | ~ m1_subset_1(E_332,k1_zfmisc_1(k2_zfmisc_1(A_334,B_333)))
      | ~ v1_funct_1(E_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2825,plain,(
    ! [A_334,B_333,E_332] :
      ( v1_funct_1(k1_partfun1(A_334,B_333,'#skF_2','#skF_1',E_332,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_332,k1_zfmisc_1(k2_zfmisc_1(A_334,B_333)))
      | ~ v1_funct_1(E_332) ) ),
    inference(resolution,[status(thm)],[c_64,c_2821])).

tff(c_2835,plain,(
    ! [A_337,B_338,E_339] :
      ( v1_funct_1(k1_partfun1(A_337,B_338,'#skF_2','#skF_1',E_339,'#skF_4'))
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338)))
      | ~ v1_funct_1(E_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2825])).

tff(c_2844,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2835])).

tff(c_2851,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_632,c_2844])).

tff(c_2855,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2851,c_678])).

tff(c_2871,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2855])).

tff(c_2993,plain,(
    ! [A_361,C_362,B_363] :
      ( k6_partfun1(A_361) = k5_relat_1(C_362,k2_funct_1(C_362))
      | k1_xboole_0 = B_363
      | ~ v2_funct_1(C_362)
      | k2_relset_1(A_361,B_363,C_362) != B_363
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_361,B_363)))
      | ~ v1_funct_2(C_362,A_361,B_363)
      | ~ v1_funct_1(C_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2999,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2993])).

tff(c_3009,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_2999])).

tff(c_3010,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3009])).

tff(c_3014,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3010,c_76])).

tff(c_3021,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74,c_58,c_3014])).

tff(c_3057,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3021,c_80])).

tff(c_3080,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3057])).

tff(c_3082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2871,c_3080])).

tff(c_3084,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2855])).

tff(c_1721,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_159])).

tff(c_3106,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3084,c_1721])).

tff(c_3209,plain,(
    ! [A_373,C_374,B_375] :
      ( k6_partfun1(A_373) = k5_relat_1(C_374,k2_funct_1(C_374))
      | k1_xboole_0 = B_375
      | ~ v2_funct_1(C_374)
      | k2_relset_1(A_373,B_375,C_374) != B_375
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_373,B_375)))
      | ~ v1_funct_2(C_374,A_373,B_375)
      | ~ v1_funct_1(C_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_3213,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3209])).

tff(c_3221,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3106,c_2805,c_3213])).

tff(c_3222,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3221])).

tff(c_3244,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3222,c_76])).

tff(c_3251,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_68,c_2805,c_3244])).

tff(c_3278,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3251,c_80])).

tff(c_3292,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3278])).

tff(c_2804,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(splitRight,[status(thm)],[c_1728])).

tff(c_3103,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k5_relat_1(B_11,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3084,c_2804])).

tff(c_5676,plain,(
    ! [B_488] :
      ( k2_funct_1('#skF_4') = B_488
      | k5_relat_1(B_488,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_488) != '#skF_2'
      | ~ v1_funct_1(B_488)
      | ~ v1_relat_1(B_488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3292,c_3103])).

tff(c_5766,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_5676])).

tff(c_5861,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_161,c_3313,c_5766])).

tff(c_5870,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5861,c_3222])).

tff(c_5873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1719,c_5870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.90/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.66  
% 7.90/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.66  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.90/2.66  
% 7.90/2.66  %Foreground sorts:
% 7.90/2.66  
% 7.90/2.66  
% 7.90/2.66  %Background operators:
% 7.90/2.66  
% 7.90/2.66  
% 7.90/2.66  %Foreground operators:
% 7.90/2.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.90/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.90/2.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.90/2.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.90/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/2.66  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.90/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.90/2.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.90/2.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.90/2.66  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.90/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.90/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.90/2.66  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.90/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.90/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.90/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.90/2.66  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.90/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.90/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.90/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.90/2.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.90/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.90/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.90/2.66  
% 7.90/2.68  tff(f_194, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.90/2.68  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.90/2.68  tff(f_97, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.90/2.68  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.90/2.68  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.90/2.68  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.90/2.68  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.90/2.68  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.90/2.68  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.90/2.68  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.90/2.68  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.90/2.68  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 7.90/2.68  tff(f_168, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.90/2.68  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.90/2.68  tff(f_126, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.90/2.68  tff(f_152, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.90/2.68  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_338, plain, (![C_103, E_104, D_99, F_102, A_101, B_100]: (k1_partfun1(A_101, B_100, C_103, D_99, E_104, F_102)=k5_relat_1(E_104, F_102) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(C_103, D_99))) | ~v1_funct_1(F_102) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_1(E_104))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.90/2.68  tff(c_342, plain, (![A_101, B_100, E_104]: (k1_partfun1(A_101, B_100, '#skF_2', '#skF_1', E_104, '#skF_4')=k5_relat_1(E_104, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_1(E_104))), inference(resolution, [status(thm)], [c_64, c_338])).
% 7.90/2.68  tff(c_421, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, '#skF_2', '#skF_1', E_118, '#skF_4')=k5_relat_1(E_118, '#skF_4') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_342])).
% 7.90/2.68  tff(c_430, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_421])).
% 7.90/2.68  tff(c_437, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_430])).
% 7.90/2.68  tff(c_32, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.90/2.68  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_198, plain, (![D_69, C_70, A_71, B_72]: (D_69=C_70 | ~r2_relset_1(A_71, B_72, C_70, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.90/2.68  tff(c_206, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_198])).
% 7.90/2.68  tff(c_221, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_206])).
% 7.90/2.68  tff(c_222, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_221])).
% 7.90/2.68  tff(c_444, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_222])).
% 7.90/2.68  tff(c_571, plain, (![D_127, C_122, E_123, B_124, F_126, A_125]: (m1_subset_1(k1_partfun1(A_125, B_124, C_122, D_127, E_123, F_126), k1_zfmisc_1(k2_zfmisc_1(A_125, D_127))) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_122, D_127))) | ~v1_funct_1(F_126) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_1(E_123))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.90/2.68  tff(c_604, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_437, c_571])).
% 7.90/2.68  tff(c_629, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_604])).
% 7.90/2.68  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_444, c_629])).
% 7.90/2.68  tff(c_632, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_221])).
% 7.90/2.68  tff(c_683, plain, (![C_132, D_137, E_133, B_134, F_136, A_135]: (v1_funct_1(k1_partfun1(A_135, B_134, C_132, D_137, E_133, F_136)) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_132, D_137))) | ~v1_funct_1(F_136) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.90/2.68  tff(c_687, plain, (![A_135, B_134, E_133]: (v1_funct_1(k1_partfun1(A_135, B_134, '#skF_2', '#skF_1', E_133, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))) | ~v1_funct_1(E_133))), inference(resolution, [status(thm)], [c_64, c_683])).
% 7.90/2.68  tff(c_697, plain, (![A_138, B_139, E_140]: (v1_funct_1(k1_partfun1(A_138, B_139, '#skF_2', '#skF_1', E_140, '#skF_4')) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_687])).
% 7.90/2.68  tff(c_706, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_697])).
% 7.90/2.68  tff(c_713, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_632, c_706])).
% 7.90/2.68  tff(c_36, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.90/2.68  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.90/2.68  tff(c_80, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 7.90/2.68  tff(c_10, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.90/2.68  tff(c_79, plain, (![A_7]: (v1_relat_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 7.90/2.68  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.90/2.68  tff(c_118, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.90/2.68  tff(c_127, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_118])).
% 7.90/2.68  tff(c_136, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_127])).
% 7.90/2.68  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_147, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.90/2.68  tff(c_156, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_147])).
% 7.90/2.68  tff(c_161, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_156])).
% 7.90/2.68  tff(c_18, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_relat_1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.90/2.68  tff(c_641, plain, (![A_128, B_129]: (k2_funct_1(A_128)=B_129 | k6_partfun1(k2_relat_1(A_128))!=k5_relat_1(B_129, A_128) | k2_relat_1(B_129)!=k1_relat_1(A_128) | ~v2_funct_1(A_128) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 7.90/2.68  tff(c_647, plain, (![B_129]: (k2_funct_1('#skF_3')=B_129 | k5_relat_1(B_129, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_129)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_129) | ~v1_relat_1(B_129) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_161, c_641])).
% 7.90/2.68  tff(c_656, plain, (![B_130]: (k2_funct_1('#skF_3')=B_130 | k5_relat_1(B_130, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_130)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_130) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74, c_58, c_647])).
% 7.90/2.68  tff(c_668, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_7))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_7)))), inference(resolution, [status(thm)], [c_79, c_656])).
% 7.90/2.68  tff(c_678, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_7 | ~v1_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_668])).
% 7.90/2.68  tff(c_717, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_713, c_678])).
% 7.90/2.68  tff(c_737, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_717])).
% 7.90/2.68  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_792, plain, (![A_156, C_157, B_158]: (k6_partfun1(A_156)=k5_relat_1(C_157, k2_funct_1(C_157)) | k1_xboole_0=B_158 | ~v2_funct_1(C_157) | k2_relset_1(A_156, B_158, C_157)!=B_158 | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_158))) | ~v1_funct_2(C_157, A_156, B_158) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.90/2.68  tff(c_798, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_792])).
% 7.90/2.68  tff(c_808, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_798])).
% 7.90/2.68  tff(c_809, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_808])).
% 7.90/2.68  tff(c_16, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.90/2.68  tff(c_76, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_partfun1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 7.90/2.68  tff(c_813, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_809, c_76])).
% 7.90/2.68  tff(c_820, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74, c_58, c_813])).
% 7.90/2.68  tff(c_853, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_820, c_80])).
% 7.90/2.68  tff(c_874, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_853])).
% 7.90/2.68  tff(c_876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_737, c_874])).
% 7.90/2.68  tff(c_878, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_717])).
% 7.90/2.68  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_124, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_118])).
% 7.90/2.68  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_124])).
% 7.90/2.68  tff(c_662, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_656])).
% 7.90/2.68  tff(c_674, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_662])).
% 7.90/2.68  tff(c_675, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_674])).
% 7.90/2.68  tff(c_679, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_675])).
% 7.90/2.68  tff(c_881, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_878, c_679])).
% 7.90/2.68  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_137, plain, (![A_59, B_60, D_61]: (r2_relset_1(A_59, B_60, D_61, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.90/2.68  tff(c_144, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_32, c_137])).
% 7.90/2.68  tff(c_159, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_147])).
% 7.90/2.68  tff(c_1706, plain, (![A_223, B_224, C_225, D_226]: (k2_relset_1(A_223, B_224, C_225)=B_224 | ~r2_relset_1(B_224, B_224, k1_partfun1(B_224, A_223, A_223, B_224, D_226, C_225), k6_partfun1(B_224)) | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1(B_224, A_223))) | ~v1_funct_2(D_226, B_224, A_223) | ~v1_funct_1(D_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_2(C_225, A_223, B_224) | ~v1_funct_1(C_225))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.90/2.68  tff(c_1712, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_632, c_1706])).
% 7.90/2.68  tff(c_1716, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_144, c_159, c_1712])).
% 7.90/2.68  tff(c_1718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_881, c_1716])).
% 7.90/2.68  tff(c_1719, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_675])).
% 7.90/2.68  tff(c_2857, plain, (![C_345, F_344, A_343, E_346, D_341, B_342]: (k1_partfun1(A_343, B_342, C_345, D_341, E_346, F_344)=k5_relat_1(E_346, F_344) | ~m1_subset_1(F_344, k1_zfmisc_1(k2_zfmisc_1(C_345, D_341))) | ~v1_funct_1(F_344) | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_343, B_342))) | ~v1_funct_1(E_346))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.90/2.68  tff(c_2861, plain, (![A_343, B_342, E_346]: (k1_partfun1(A_343, B_342, '#skF_2', '#skF_1', E_346, '#skF_4')=k5_relat_1(E_346, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_343, B_342))) | ~v1_funct_1(E_346))), inference(resolution, [status(thm)], [c_64, c_2857])).
% 7.90/2.68  tff(c_3297, plain, (![A_376, B_377, E_378]: (k1_partfun1(A_376, B_377, '#skF_2', '#skF_1', E_378, '#skF_4')=k5_relat_1(E_378, '#skF_4') | ~m1_subset_1(E_378, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))) | ~v1_funct_1(E_378))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2861])).
% 7.90/2.68  tff(c_3306, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_3297])).
% 7.90/2.68  tff(c_3313, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_632, c_3306])).
% 7.90/2.68  tff(c_1720, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_675])).
% 7.90/2.68  tff(c_75, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_partfun1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 7.90/2.68  tff(c_1724, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1720, c_75])).
% 7.90/2.68  tff(c_1728, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_68, c_1724])).
% 7.90/2.68  tff(c_1736, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1728])).
% 7.90/2.68  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_194])).
% 7.90/2.68  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.90/2.68  tff(c_78, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12])).
% 7.90/2.68  tff(c_2787, plain, (![C_323, D_324, B_322, E_325, A_321]: (k1_xboole_0=C_323 | v2_funct_1(E_325) | k2_relset_1(A_321, B_322, D_324)!=B_322 | ~v2_funct_1(k1_partfun1(A_321, B_322, B_322, C_323, D_324, E_325)) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(B_322, C_323))) | ~v1_funct_2(E_325, B_322, C_323) | ~v1_funct_1(E_325) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))) | ~v1_funct_2(D_324, A_321, B_322) | ~v1_funct_1(D_324))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.90/2.68  tff(c_2793, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_632, c_2787])).
% 7.90/2.68  tff(c_2801, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_78, c_62, c_2793])).
% 7.90/2.68  tff(c_2803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1736, c_56, c_2801])).
% 7.90/2.68  tff(c_2805, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1728])).
% 7.90/2.68  tff(c_2821, plain, (![C_331, B_333, F_335, D_336, A_334, E_332]: (v1_funct_1(k1_partfun1(A_334, B_333, C_331, D_336, E_332, F_335)) | ~m1_subset_1(F_335, k1_zfmisc_1(k2_zfmisc_1(C_331, D_336))) | ~v1_funct_1(F_335) | ~m1_subset_1(E_332, k1_zfmisc_1(k2_zfmisc_1(A_334, B_333))) | ~v1_funct_1(E_332))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.90/2.68  tff(c_2825, plain, (![A_334, B_333, E_332]: (v1_funct_1(k1_partfun1(A_334, B_333, '#skF_2', '#skF_1', E_332, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_332, k1_zfmisc_1(k2_zfmisc_1(A_334, B_333))) | ~v1_funct_1(E_332))), inference(resolution, [status(thm)], [c_64, c_2821])).
% 7.90/2.68  tff(c_2835, plain, (![A_337, B_338, E_339]: (v1_funct_1(k1_partfun1(A_337, B_338, '#skF_2', '#skF_1', E_339, '#skF_4')) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))) | ~v1_funct_1(E_339))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2825])).
% 7.90/2.68  tff(c_2844, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2835])).
% 7.90/2.68  tff(c_2851, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_632, c_2844])).
% 7.90/2.68  tff(c_2855, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2851, c_678])).
% 7.90/2.68  tff(c_2871, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2855])).
% 7.90/2.68  tff(c_2993, plain, (![A_361, C_362, B_363]: (k6_partfun1(A_361)=k5_relat_1(C_362, k2_funct_1(C_362)) | k1_xboole_0=B_363 | ~v2_funct_1(C_362) | k2_relset_1(A_361, B_363, C_362)!=B_363 | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_361, B_363))) | ~v1_funct_2(C_362, A_361, B_363) | ~v1_funct_1(C_362))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.90/2.68  tff(c_2999, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2993])).
% 7.90/2.68  tff(c_3009, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_2999])).
% 7.90/2.68  tff(c_3010, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_3009])).
% 7.90/2.68  tff(c_3014, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3010, c_76])).
% 7.90/2.68  tff(c_3021, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74, c_58, c_3014])).
% 7.90/2.68  tff(c_3057, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3021, c_80])).
% 7.90/2.68  tff(c_3080, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3057])).
% 7.90/2.68  tff(c_3082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2871, c_3080])).
% 7.90/2.68  tff(c_3084, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2855])).
% 7.90/2.68  tff(c_1721, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1720, c_159])).
% 7.90/2.68  tff(c_3106, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3084, c_1721])).
% 7.90/2.68  tff(c_3209, plain, (![A_373, C_374, B_375]: (k6_partfun1(A_373)=k5_relat_1(C_374, k2_funct_1(C_374)) | k1_xboole_0=B_375 | ~v2_funct_1(C_374) | k2_relset_1(A_373, B_375, C_374)!=B_375 | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_373, B_375))) | ~v1_funct_2(C_374, A_373, B_375) | ~v1_funct_1(C_374))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.90/2.68  tff(c_3213, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_3209])).
% 7.90/2.68  tff(c_3221, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3106, c_2805, c_3213])).
% 7.90/2.68  tff(c_3222, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_3221])).
% 7.90/2.68  tff(c_3244, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3222, c_76])).
% 7.90/2.68  tff(c_3251, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_68, c_2805, c_3244])).
% 7.90/2.68  tff(c_3278, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3251, c_80])).
% 7.90/2.68  tff(c_3292, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3278])).
% 7.90/2.68  tff(c_2804, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(splitRight, [status(thm)], [c_1728])).
% 7.90/2.68  tff(c_3103, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k5_relat_1(B_11, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_3084, c_2804])).
% 7.90/2.68  tff(c_5676, plain, (![B_488]: (k2_funct_1('#skF_4')=B_488 | k5_relat_1(B_488, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_488)!='#skF_2' | ~v1_funct_1(B_488) | ~v1_relat_1(B_488))), inference(demodulation, [status(thm), theory('equality')], [c_3292, c_3103])).
% 7.90/2.68  tff(c_5766, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_136, c_5676])).
% 7.90/2.68  tff(c_5861, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_161, c_3313, c_5766])).
% 7.90/2.68  tff(c_5870, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5861, c_3222])).
% 7.90/2.68  tff(c_5873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1719, c_5870])).
% 7.90/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.68  
% 7.90/2.68  Inference rules
% 7.90/2.68  ----------------------
% 7.90/2.68  #Ref     : 0
% 7.90/2.68  #Sup     : 1208
% 7.90/2.68  #Fact    : 0
% 7.90/2.68  #Define  : 0
% 7.90/2.69  #Split   : 30
% 7.90/2.69  #Chain   : 0
% 7.90/2.69  #Close   : 0
% 7.90/2.69  
% 7.90/2.69  Ordering : KBO
% 7.90/2.69  
% 7.90/2.69  Simplification rules
% 7.90/2.69  ----------------------
% 7.90/2.69  #Subsume      : 84
% 7.90/2.69  #Demod        : 2198
% 7.90/2.69  #Tautology    : 338
% 7.90/2.69  #SimpNegUnit  : 153
% 7.90/2.69  #BackRed      : 56
% 7.90/2.69  
% 7.90/2.69  #Partial instantiations: 0
% 7.90/2.69  #Strategies tried      : 1
% 7.90/2.69  
% 7.90/2.69  Timing (in seconds)
% 7.90/2.69  ----------------------
% 7.90/2.69  Preprocessing        : 0.37
% 7.90/2.69  Parsing              : 0.19
% 7.90/2.69  CNF conversion       : 0.02
% 7.90/2.69  Main loop            : 1.54
% 7.90/2.69  Inferencing          : 0.47
% 7.90/2.69  Reduction            : 0.64
% 7.90/2.69  Demodulation         : 0.50
% 7.90/2.69  BG Simplification    : 0.08
% 7.90/2.69  Subsumption          : 0.26
% 7.90/2.69  Abstraction          : 0.07
% 7.90/2.69  MUC search           : 0.00
% 7.90/2.69  Cooper               : 0.00
% 7.90/2.69  Total                : 1.96
% 7.90/2.69  Index Insertion      : 0.00
% 7.90/2.69  Index Deletion       : 0.00
% 7.90/2.69  Index Matching       : 0.00
% 7.90/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
