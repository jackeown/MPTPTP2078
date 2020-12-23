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
% DateTime   : Thu Dec  3 10:13:25 EST 2020

% Result     : Theorem 10.98s
% Output     : CNFRefutation 10.98s
% Verified   : 
% Statistics : Number of formulae       :  165 (1439 expanded)
%              Number of leaves         :   41 ( 520 expanded)
%              Depth                    :   25
%              Number of atoms          :  423 (6052 expanded)
%              Number of equality atoms :  165 (2097 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_192,negated_conjecture,(
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

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_107,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
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

tff(f_166,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_124,axiom,(
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

tff(f_40,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_150,axiom,(
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

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_323,plain,(
    ! [C_103,E_104,D_99,F_102,A_101,B_100] :
      ( k1_partfun1(A_101,B_100,C_103,D_99,E_104,F_102) = k5_relat_1(E_104,F_102)
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(C_103,D_99)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_1(E_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_329,plain,(
    ! [A_101,B_100,E_104] :
      ( k1_partfun1(A_101,B_100,'#skF_2','#skF_1',E_104,'#skF_4') = k5_relat_1(E_104,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_1(E_104) ) ),
    inference(resolution,[status(thm)],[c_62,c_323])).

tff(c_340,plain,(
    ! [A_109,B_110,E_111] :
      ( k1_partfun1(A_109,B_110,'#skF_2','#skF_1',E_111,'#skF_4') = k5_relat_1(E_111,'#skF_4')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_329])).

tff(c_346,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_340])).

tff(c_353,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_346])).

tff(c_30,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_193,plain,(
    ! [D_69,C_70,A_71,B_72] :
      ( D_69 = C_70
      | ~ r2_relset_1(A_71,B_72,C_70,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_201,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_193])).

tff(c_216,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_201])).

tff(c_217,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_358,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_217])).

tff(c_498,plain,(
    ! [D_130,F_129,C_125,E_126,A_128,B_127] :
      ( m1_subset_1(k1_partfun1(A_128,B_127,C_125,D_130,E_126,F_129),k1_zfmisc_1(k2_zfmisc_1(A_128,D_130)))
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_125,D_130)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_1(E_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_540,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_498])).

tff(c_562,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_540])).

tff(c_564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_562])).

tff(c_565,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_612,plain,(
    ! [B_137,A_138,F_139,E_136,D_140,C_135] :
      ( v1_funct_1(k1_partfun1(A_138,B_137,C_135,D_140,E_136,F_139))
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_135,D_140)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_618,plain,(
    ! [A_138,B_137,E_136] :
      ( v1_funct_1(k1_partfun1(A_138,B_137,'#skF_2','#skF_1',E_136,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_136) ) ),
    inference(resolution,[status(thm)],[c_62,c_612])).

tff(c_643,plain,(
    ! [A_144,B_145,E_146] :
      ( v1_funct_1(k1_partfun1(A_144,B_145,'#skF_2','#skF_1',E_146,'#skF_4'))
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_1(E_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_618])).

tff(c_649,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_643])).

tff(c_656,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_565,c_649])).

tff(c_34,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_112,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [A_25] :
      ( v1_relat_1(k6_partfun1(A_25))
      | ~ v1_relat_1(k2_zfmisc_1(A_25,A_25)) ) ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_124,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_115])).

tff(c_118,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_112])).

tff(c_127,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_118])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_142,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_148,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_142])).

tff(c_155,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_148])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_relat_1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_574,plain,(
    ! [A_131,B_132] :
      ( k2_funct_1(A_131) = B_132
      | k6_partfun1(k2_relat_1(A_131)) != k5_relat_1(B_132,A_131)
      | k2_relat_1(B_132) != k1_relat_1(A_131)
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_578,plain,(
    ! [B_132] :
      ( k2_funct_1('#skF_3') = B_132
      | k5_relat_1(B_132,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_132) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_574])).

tff(c_585,plain,(
    ! [B_133] :
      ( k2_funct_1('#skF_3') = B_133
      | k5_relat_1(B_133,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_133) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_56,c_578])).

tff(c_588,plain,(
    ! [A_25] :
      ( k6_partfun1(A_25) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_25),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_25)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_124,c_585])).

tff(c_599,plain,(
    ! [A_25] :
      ( k6_partfun1(A_25) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_25),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_25
      | ~ v1_funct_1(k6_partfun1(A_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_588])).

tff(c_663,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_656,c_599])).

tff(c_666,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_663])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_737,plain,(
    ! [A_162,C_163,B_164] :
      ( k6_partfun1(A_162) = k5_relat_1(C_163,k2_funct_1(C_163))
      | k1_xboole_0 = B_164
      | ~ v2_funct_1(C_163)
      | k2_relset_1(A_162,B_164,C_163) != B_164
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_164)))
      | ~ v1_funct_2(C_163,A_162,B_164)
      | ~ v1_funct_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_741,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_737])).

tff(c_749,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_741])).

tff(c_750,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_749])).

tff(c_14,plain,(
    ! [A_8] :
      ( k1_relat_1(k5_relat_1(A_8,k2_funct_1(A_8))) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_758,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_14])).

tff(c_765,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_56,c_76,c_758])).

tff(c_767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_666,c_765])).

tff(c_769,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_663])).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_121,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_112])).

tff(c_130,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_591,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_585])).

tff(c_602,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_591])).

tff(c_603,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_602])).

tff(c_608,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_603])).

tff(c_772,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_608])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_132,plain,(
    ! [A_59,B_60,D_61] :
      ( r2_relset_1(A_59,B_60,D_61,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_139,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_30,c_132])).

tff(c_156,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_142])).

tff(c_1527,plain,(
    ! [A_227,B_228,C_229,D_230] :
      ( k2_relset_1(A_227,B_228,C_229) = B_228
      | ~ r2_relset_1(B_228,B_228,k1_partfun1(B_228,A_227,A_227,B_228,D_230,C_229),k6_partfun1(B_228))
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_zfmisc_1(B_228,A_227)))
      | ~ v1_funct_2(D_230,B_228,A_227)
      | ~ v1_funct_1(D_230)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ v1_funct_2(C_229,A_227,B_228)
      | ~ v1_funct_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1533,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_1527])).

tff(c_1537,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_139,c_156,c_1533])).

tff(c_1539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_772,c_1537])).

tff(c_1540,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_603])).

tff(c_2494,plain,(
    ! [E_341,F_339,C_340,D_336,A_338,B_337] :
      ( k1_partfun1(A_338,B_337,C_340,D_336,E_341,F_339) = k5_relat_1(E_341,F_339)
      | ~ m1_subset_1(F_339,k1_zfmisc_1(k2_zfmisc_1(C_340,D_336)))
      | ~ v1_funct_1(F_339)
      | ~ m1_subset_1(E_341,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337)))
      | ~ v1_funct_1(E_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2500,plain,(
    ! [A_338,B_337,E_341] :
      ( k1_partfun1(A_338,B_337,'#skF_2','#skF_1',E_341,'#skF_4') = k5_relat_1(E_341,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_341,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337)))
      | ~ v1_funct_1(E_341) ) ),
    inference(resolution,[status(thm)],[c_62,c_2494])).

tff(c_2737,plain,(
    ! [A_363,B_364,E_365] :
      ( k1_partfun1(A_363,B_364,'#skF_2','#skF_1',E_365,'#skF_4') = k5_relat_1(E_365,'#skF_4')
      | ~ m1_subset_1(E_365,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364)))
      | ~ v1_funct_1(E_365) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2500])).

tff(c_2743,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2737])).

tff(c_2750,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_565,c_2743])).

tff(c_1541,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_603])).

tff(c_73,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_partfun1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_1545,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_73])).

tff(c_1549,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_66,c_1545])).

tff(c_1557,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1549])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_10,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_2440,plain,(
    ! [E_320,B_317,C_318,D_319,A_316] :
      ( k1_xboole_0 = C_318
      | v2_funct_1(E_320)
      | k2_relset_1(A_316,B_317,D_319) != B_317
      | ~ v2_funct_1(k1_partfun1(A_316,B_317,B_317,C_318,D_319,E_320))
      | ~ m1_subset_1(E_320,k1_zfmisc_1(k2_zfmisc_1(B_317,C_318)))
      | ~ v1_funct_2(E_320,B_317,C_318)
      | ~ v1_funct_1(E_320)
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ v1_funct_2(D_319,A_316,B_317)
      | ~ v1_funct_1(D_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2446,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_565,c_2440])).

tff(c_2454,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_74,c_60,c_2446])).

tff(c_2456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1557,c_54,c_2454])).

tff(c_2458,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1549])).

tff(c_1542,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_156])).

tff(c_2557,plain,(
    ! [B_349,C_350,A_351] :
      ( k6_partfun1(B_349) = k5_relat_1(k2_funct_1(C_350),C_350)
      | k1_xboole_0 = B_349
      | ~ v2_funct_1(C_350)
      | k2_relset_1(A_351,B_349,C_350) != B_349
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_351,B_349)))
      | ~ v1_funct_2(C_350,A_351,B_349)
      | ~ v1_funct_1(C_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2563,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2557])).

tff(c_2573,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1542,c_2458,c_2563])).

tff(c_2574,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2573])).

tff(c_2584,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2574])).

tff(c_2615,plain,(
    ! [A_356,C_357,B_358] :
      ( k6_partfun1(A_356) = k5_relat_1(C_357,k2_funct_1(C_357))
      | k1_xboole_0 = B_358
      | ~ v2_funct_1(C_357)
      | k2_relset_1(A_356,B_358,C_357) != B_358
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(A_356,B_358)))
      | ~ v1_funct_2(C_357,A_356,B_358)
      | ~ v1_funct_1(C_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2619,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2615])).

tff(c_2627,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_2619])).

tff(c_2628,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2627])).

tff(c_2636,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_14])).

tff(c_2643,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_56,c_76,c_2636])).

tff(c_2645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2584,c_2643])).

tff(c_2647,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2574])).

tff(c_2652,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_1542])).

tff(c_2687,plain,(
    ! [A_360,C_361,B_362] :
      ( k6_partfun1(A_360) = k5_relat_1(C_361,k2_funct_1(C_361))
      | k1_xboole_0 = B_362
      | ~ v2_funct_1(C_361)
      | k2_relset_1(A_360,B_362,C_361) != B_362
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_360,B_362)))
      | ~ v1_funct_2(C_361,A_360,B_362)
      | ~ v1_funct_1(C_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2693,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2687])).

tff(c_2703,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2652,c_2458,c_2693])).

tff(c_2704,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2703])).

tff(c_2722,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2704,c_14])).

tff(c_2729,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_66,c_2458,c_76,c_2722])).

tff(c_2457,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(splitRight,[status(thm)],[c_1549])).

tff(c_2649,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k5_relat_1(B_11,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_2457])).

tff(c_4786,plain,(
    ! [B_462] :
      ( k2_funct_1('#skF_4') = B_462
      | k5_relat_1(B_462,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_462) != '#skF_2'
      | ~ v1_funct_1(B_462)
      | ~ v1_relat_1(B_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2729,c_2649])).

tff(c_4882,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_4786])).

tff(c_4976,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_155,c_2750,c_4882])).

tff(c_4979,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4976,c_2704])).

tff(c_4982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1540,c_4979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.98/3.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.98/3.83  
% 10.98/3.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.98/3.83  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.98/3.83  
% 10.98/3.83  %Foreground sorts:
% 10.98/3.83  
% 10.98/3.83  
% 10.98/3.83  %Background operators:
% 10.98/3.83  
% 10.98/3.83  
% 10.98/3.83  %Foreground operators:
% 10.98/3.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.98/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.98/3.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.98/3.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.98/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.98/3.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.98/3.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.98/3.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.98/3.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.98/3.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.98/3.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.98/3.83  tff('#skF_2', type, '#skF_2': $i).
% 10.98/3.83  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.98/3.83  tff('#skF_3', type, '#skF_3': $i).
% 10.98/3.83  tff('#skF_1', type, '#skF_1': $i).
% 10.98/3.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.98/3.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.98/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.98/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.98/3.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.98/3.83  tff('#skF_4', type, '#skF_4': $i).
% 10.98/3.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.98/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.98/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.98/3.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.98/3.83  
% 10.98/3.90  tff(f_192, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 10.98/3.90  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.98/3.90  tff(f_95, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.98/3.90  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.98/3.90  tff(f_91, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.98/3.90  tff(f_107, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.98/3.90  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.98/3.90  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.98/3.90  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.98/3.90  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.98/3.90  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 10.98/3.90  tff(f_166, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 10.98/3.90  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 10.98/3.90  tff(f_124, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 10.98/3.90  tff(f_40, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 10.98/3.90  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 10.98/3.90  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_323, plain, (![C_103, E_104, D_99, F_102, A_101, B_100]: (k1_partfun1(A_101, B_100, C_103, D_99, E_104, F_102)=k5_relat_1(E_104, F_102) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(C_103, D_99))) | ~v1_funct_1(F_102) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_1(E_104))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.98/3.90  tff(c_329, plain, (![A_101, B_100, E_104]: (k1_partfun1(A_101, B_100, '#skF_2', '#skF_1', E_104, '#skF_4')=k5_relat_1(E_104, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_1(E_104))), inference(resolution, [status(thm)], [c_62, c_323])).
% 10.98/3.90  tff(c_340, plain, (![A_109, B_110, E_111]: (k1_partfun1(A_109, B_110, '#skF_2', '#skF_1', E_111, '#skF_4')=k5_relat_1(E_111, '#skF_4') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_1(E_111))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_329])).
% 10.98/3.90  tff(c_346, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_340])).
% 10.98/3.90  tff(c_353, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_346])).
% 10.98/3.90  tff(c_30, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.98/3.90  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_193, plain, (![D_69, C_70, A_71, B_72]: (D_69=C_70 | ~r2_relset_1(A_71, B_72, C_70, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.98/3.90  tff(c_201, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_193])).
% 10.98/3.90  tff(c_216, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_201])).
% 10.98/3.90  tff(c_217, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_216])).
% 10.98/3.90  tff(c_358, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_217])).
% 10.98/3.90  tff(c_498, plain, (![D_130, F_129, C_125, E_126, A_128, B_127]: (m1_subset_1(k1_partfun1(A_128, B_127, C_125, D_130, E_126, F_129), k1_zfmisc_1(k2_zfmisc_1(A_128, D_130))) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_125, D_130))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_1(E_126))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.98/3.90  tff(c_540, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_353, c_498])).
% 10.98/3.90  tff(c_562, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_540])).
% 10.98/3.90  tff(c_564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_562])).
% 10.98/3.90  tff(c_565, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_216])).
% 10.98/3.90  tff(c_612, plain, (![B_137, A_138, F_139, E_136, D_140, C_135]: (v1_funct_1(k1_partfun1(A_138, B_137, C_135, D_140, E_136, F_139)) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_135, D_140))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_136))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.98/3.90  tff(c_618, plain, (![A_138, B_137, E_136]: (v1_funct_1(k1_partfun1(A_138, B_137, '#skF_2', '#skF_1', E_136, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_136))), inference(resolution, [status(thm)], [c_62, c_612])).
% 10.98/3.90  tff(c_643, plain, (![A_144, B_145, E_146]: (v1_funct_1(k1_partfun1(A_144, B_145, '#skF_2', '#skF_1', E_146, '#skF_4')) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_1(E_146))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_618])).
% 10.98/3.90  tff(c_649, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_643])).
% 10.98/3.90  tff(c_656, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_565, c_649])).
% 10.98/3.90  tff(c_34, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.98/3.90  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.98/3.90  tff(c_75, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 10.98/3.90  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.98/3.90  tff(c_112, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.98/3.90  tff(c_115, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)) | ~v1_relat_1(k2_zfmisc_1(A_25, A_25)))), inference(resolution, [status(thm)], [c_30, c_112])).
% 10.98/3.90  tff(c_124, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_115])).
% 10.98/3.90  tff(c_118, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_112])).
% 10.98/3.90  tff(c_127, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_118])).
% 10.98/3.90  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_142, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.98/3.90  tff(c_148, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_142])).
% 10.98/3.90  tff(c_155, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_148])).
% 10.98/3.90  tff(c_16, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_relat_1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.98/3.90  tff(c_574, plain, (![A_131, B_132]: (k2_funct_1(A_131)=B_132 | k6_partfun1(k2_relat_1(A_131))!=k5_relat_1(B_132, A_131) | k2_relat_1(B_132)!=k1_relat_1(A_131) | ~v2_funct_1(A_131) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 10.98/3.90  tff(c_578, plain, (![B_132]: (k2_funct_1('#skF_3')=B_132 | k5_relat_1(B_132, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_132)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_132) | ~v1_relat_1(B_132) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_574])).
% 10.98/3.90  tff(c_585, plain, (![B_133]: (k2_funct_1('#skF_3')=B_133 | k5_relat_1(B_133, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_133)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_133) | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_56, c_578])).
% 10.98/3.90  tff(c_588, plain, (![A_25]: (k6_partfun1(A_25)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_25), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_25))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_124, c_585])).
% 10.98/3.90  tff(c_599, plain, (![A_25]: (k6_partfun1(A_25)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_25), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_25 | ~v1_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_588])).
% 10.98/3.90  tff(c_663, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_656, c_599])).
% 10.98/3.90  tff(c_666, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_663])).
% 10.98/3.90  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.98/3.90  tff(c_76, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 10.98/3.90  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_737, plain, (![A_162, C_163, B_164]: (k6_partfun1(A_162)=k5_relat_1(C_163, k2_funct_1(C_163)) | k1_xboole_0=B_164 | ~v2_funct_1(C_163) | k2_relset_1(A_162, B_164, C_163)!=B_164 | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_164))) | ~v1_funct_2(C_163, A_162, B_164) | ~v1_funct_1(C_163))), inference(cnfTransformation, [status(thm)], [f_166])).
% 10.98/3.90  tff(c_741, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_737])).
% 10.98/3.90  tff(c_749, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_741])).
% 10.98/3.90  tff(c_750, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_749])).
% 10.98/3.90  tff(c_14, plain, (![A_8]: (k1_relat_1(k5_relat_1(A_8, k2_funct_1(A_8)))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.98/3.90  tff(c_758, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_750, c_14])).
% 10.98/3.90  tff(c_765, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_56, c_76, c_758])).
% 10.98/3.90  tff(c_767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_666, c_765])).
% 10.98/3.90  tff(c_769, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_663])).
% 10.98/3.90  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_121, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_112])).
% 10.98/3.90  tff(c_130, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_121])).
% 10.98/3.90  tff(c_591, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_130, c_585])).
% 10.98/3.90  tff(c_602, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_591])).
% 10.98/3.90  tff(c_603, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_602])).
% 10.98/3.90  tff(c_608, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_603])).
% 10.98/3.90  tff(c_772, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_769, c_608])).
% 10.98/3.90  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_132, plain, (![A_59, B_60, D_61]: (r2_relset_1(A_59, B_60, D_61, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.98/3.90  tff(c_139, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_30, c_132])).
% 10.98/3.90  tff(c_156, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_142])).
% 10.98/3.90  tff(c_1527, plain, (![A_227, B_228, C_229, D_230]: (k2_relset_1(A_227, B_228, C_229)=B_228 | ~r2_relset_1(B_228, B_228, k1_partfun1(B_228, A_227, A_227, B_228, D_230, C_229), k6_partfun1(B_228)) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_zfmisc_1(B_228, A_227))) | ~v1_funct_2(D_230, B_228, A_227) | ~v1_funct_1(D_230) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | ~v1_funct_2(C_229, A_227, B_228) | ~v1_funct_1(C_229))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.98/3.90  tff(c_1533, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_565, c_1527])).
% 10.98/3.90  tff(c_1537, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_139, c_156, c_1533])).
% 10.98/3.90  tff(c_1539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_772, c_1537])).
% 10.98/3.90  tff(c_1540, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_603])).
% 10.98/3.90  tff(c_2494, plain, (![E_341, F_339, C_340, D_336, A_338, B_337]: (k1_partfun1(A_338, B_337, C_340, D_336, E_341, F_339)=k5_relat_1(E_341, F_339) | ~m1_subset_1(F_339, k1_zfmisc_1(k2_zfmisc_1(C_340, D_336))) | ~v1_funct_1(F_339) | ~m1_subset_1(E_341, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))) | ~v1_funct_1(E_341))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.98/3.90  tff(c_2500, plain, (![A_338, B_337, E_341]: (k1_partfun1(A_338, B_337, '#skF_2', '#skF_1', E_341, '#skF_4')=k5_relat_1(E_341, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_341, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))) | ~v1_funct_1(E_341))), inference(resolution, [status(thm)], [c_62, c_2494])).
% 10.98/3.90  tff(c_2737, plain, (![A_363, B_364, E_365]: (k1_partfun1(A_363, B_364, '#skF_2', '#skF_1', E_365, '#skF_4')=k5_relat_1(E_365, '#skF_4') | ~m1_subset_1(E_365, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))) | ~v1_funct_1(E_365))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2500])).
% 10.98/3.90  tff(c_2743, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2737])).
% 10.98/3.90  tff(c_2750, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_565, c_2743])).
% 10.98/3.90  tff(c_1541, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_603])).
% 10.98/3.90  tff(c_73, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_partfun1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 10.98/3.90  tff(c_1545, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1541, c_73])).
% 10.98/3.90  tff(c_1549, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_66, c_1545])).
% 10.98/3.90  tff(c_1557, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1549])).
% 10.98/3.90  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.98/3.90  tff(c_10, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.98/3.90  tff(c_74, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 10.98/3.90  tff(c_2440, plain, (![E_320, B_317, C_318, D_319, A_316]: (k1_xboole_0=C_318 | v2_funct_1(E_320) | k2_relset_1(A_316, B_317, D_319)!=B_317 | ~v2_funct_1(k1_partfun1(A_316, B_317, B_317, C_318, D_319, E_320)) | ~m1_subset_1(E_320, k1_zfmisc_1(k2_zfmisc_1(B_317, C_318))) | ~v1_funct_2(E_320, B_317, C_318) | ~v1_funct_1(E_320) | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))) | ~v1_funct_2(D_319, A_316, B_317) | ~v1_funct_1(D_319))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.98/3.90  tff(c_2446, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_565, c_2440])).
% 10.98/3.90  tff(c_2454, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_74, c_60, c_2446])).
% 10.98/3.90  tff(c_2456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1557, c_54, c_2454])).
% 10.98/3.90  tff(c_2458, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1549])).
% 10.98/3.90  tff(c_1542, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_156])).
% 10.98/3.90  tff(c_2557, plain, (![B_349, C_350, A_351]: (k6_partfun1(B_349)=k5_relat_1(k2_funct_1(C_350), C_350) | k1_xboole_0=B_349 | ~v2_funct_1(C_350) | k2_relset_1(A_351, B_349, C_350)!=B_349 | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_351, B_349))) | ~v1_funct_2(C_350, A_351, B_349) | ~v1_funct_1(C_350))), inference(cnfTransformation, [status(thm)], [f_166])).
% 10.98/3.90  tff(c_2563, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2557])).
% 10.98/3.90  tff(c_2573, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1542, c_2458, c_2563])).
% 10.98/3.90  tff(c_2574, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_2573])).
% 10.98/3.90  tff(c_2584, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2574])).
% 10.98/3.90  tff(c_2615, plain, (![A_356, C_357, B_358]: (k6_partfun1(A_356)=k5_relat_1(C_357, k2_funct_1(C_357)) | k1_xboole_0=B_358 | ~v2_funct_1(C_357) | k2_relset_1(A_356, B_358, C_357)!=B_358 | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(A_356, B_358))) | ~v1_funct_2(C_357, A_356, B_358) | ~v1_funct_1(C_357))), inference(cnfTransformation, [status(thm)], [f_166])).
% 10.98/3.90  tff(c_2619, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2615])).
% 10.98/3.90  tff(c_2627, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_2619])).
% 10.98/3.90  tff(c_2628, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_2627])).
% 10.98/3.90  tff(c_2636, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2628, c_14])).
% 10.98/3.90  tff(c_2643, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_56, c_76, c_2636])).
% 10.98/3.90  tff(c_2645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2584, c_2643])).
% 10.98/3.90  tff(c_2647, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2574])).
% 10.98/3.90  tff(c_2652, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_1542])).
% 10.98/3.90  tff(c_2687, plain, (![A_360, C_361, B_362]: (k6_partfun1(A_360)=k5_relat_1(C_361, k2_funct_1(C_361)) | k1_xboole_0=B_362 | ~v2_funct_1(C_361) | k2_relset_1(A_360, B_362, C_361)!=B_362 | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_360, B_362))) | ~v1_funct_2(C_361, A_360, B_362) | ~v1_funct_1(C_361))), inference(cnfTransformation, [status(thm)], [f_166])).
% 10.98/3.90  tff(c_2693, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2687])).
% 10.98/3.90  tff(c_2703, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2652, c_2458, c_2693])).
% 10.98/3.90  tff(c_2704, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_2703])).
% 10.98/3.90  tff(c_2722, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2704, c_14])).
% 10.98/3.90  tff(c_2729, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_66, c_2458, c_76, c_2722])).
% 10.98/3.90  tff(c_2457, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(splitRight, [status(thm)], [c_1549])).
% 10.98/3.90  tff(c_2649, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k5_relat_1(B_11, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_2457])).
% 10.98/3.90  tff(c_4786, plain, (![B_462]: (k2_funct_1('#skF_4')=B_462 | k5_relat_1(B_462, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_462)!='#skF_2' | ~v1_funct_1(B_462) | ~v1_relat_1(B_462))), inference(demodulation, [status(thm), theory('equality')], [c_2729, c_2649])).
% 10.98/3.90  tff(c_4882, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_127, c_4786])).
% 10.98/3.90  tff(c_4976, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_155, c_2750, c_4882])).
% 10.98/3.90  tff(c_4979, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4976, c_2704])).
% 10.98/3.90  tff(c_4982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1540, c_4979])).
% 10.98/3.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.98/3.90  
% 10.98/3.90  Inference rules
% 10.98/3.90  ----------------------
% 10.98/3.90  #Ref     : 0
% 10.98/3.90  #Sup     : 1006
% 10.98/3.90  #Fact    : 0
% 10.98/3.90  #Define  : 0
% 10.98/3.90  #Split   : 29
% 10.98/3.90  #Chain   : 0
% 10.98/3.90  #Close   : 0
% 10.98/3.90  
% 10.98/3.90  Ordering : KBO
% 10.98/3.90  
% 10.98/3.90  Simplification rules
% 10.98/3.90  ----------------------
% 10.98/3.90  #Subsume      : 46
% 10.98/3.90  #Demod        : 1439
% 10.98/3.90  #Tautology    : 260
% 10.98/3.90  #SimpNegUnit  : 94
% 10.98/3.90  #BackRed      : 51
% 10.98/3.90  
% 10.98/3.90  #Partial instantiations: 0
% 10.98/3.90  #Strategies tried      : 1
% 10.98/3.90  
% 10.98/3.90  Timing (in seconds)
% 10.98/3.90  ----------------------
% 10.98/3.90  Preprocessing        : 0.59
% 10.98/3.90  Parsing              : 0.31
% 10.98/3.90  CNF conversion       : 0.04
% 10.98/3.90  Main loop            : 2.33
% 10.98/3.90  Inferencing          : 0.79
% 10.98/3.90  Reduction            : 0.92
% 10.98/3.90  Demodulation         : 0.69
% 10.98/3.90  BG Simplification    : 0.08
% 10.98/3.90  Subsumption          : 0.39
% 10.98/3.91  Abstraction          : 0.10
% 11.40/3.91  MUC search           : 0.00
% 11.40/3.91  Cooper               : 0.00
% 11.40/3.91  Total                : 3.03
% 11.40/3.91  Index Insertion      : 0.00
% 11.40/3.91  Index Deletion       : 0.00
% 11.40/3.91  Index Matching       : 0.00
% 11.40/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
