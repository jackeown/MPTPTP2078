%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:59 EST 2020

% Result     : Theorem 6.64s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 570 expanded)
%              Number of leaves         :   44 ( 217 expanded)
%              Depth                    :   15
%              Number of atoms          :  318 (2345 expanded)
%              Number of equality atoms :   92 ( 829 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_208,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_182,axiom,(
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

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_99,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_140,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_166,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_108,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_121,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_108])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_220,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_233,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_220])).

tff(c_2528,plain,(
    ! [A_178,C_179,B_180] :
      ( k6_partfun1(A_178) = k5_relat_1(C_179,k2_funct_1(C_179))
      | k1_xboole_0 = B_180
      | ~ v2_funct_1(C_179)
      | k2_relset_1(A_178,B_180,C_179) != B_180
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_180)))
      | ~ v1_funct_2(C_179,A_178,B_180)
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2534,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2528])).

tff(c_2544,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_233,c_2534])).

tff(c_2545,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2544])).

tff(c_2572,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2545])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_44,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_83,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_161,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_168,plain,(
    ! [A_27] : r2_relset_1(A_27,A_27,k6_partfun1(A_27),k6_partfun1(A_27)) ),
    inference(resolution,[status(thm)],[c_83,c_161])).

tff(c_932,plain,(
    ! [E_115,A_112,D_113,B_116,C_117,F_114] :
      ( k1_partfun1(A_112,B_116,C_117,D_113,E_115,F_114) = k5_relat_1(E_115,F_114)
      | ~ m1_subset_1(F_114,k1_zfmisc_1(k2_zfmisc_1(C_117,D_113)))
      | ~ v1_funct_1(F_114)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_116)))
      | ~ v1_funct_1(E_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_938,plain,(
    ! [A_112,B_116,E_115] :
      ( k1_partfun1(A_112,B_116,'#skF_2','#skF_1',E_115,'#skF_4') = k5_relat_1(E_115,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_116)))
      | ~ v1_funct_1(E_115) ) ),
    inference(resolution,[status(thm)],[c_72,c_932])).

tff(c_1363,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_2','#skF_1',E_136,'#skF_4') = k5_relat_1(E_136,'#skF_4')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_938])).

tff(c_1369,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1363])).

tff(c_1376,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1369])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_491,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_499,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_491])).

tff(c_514,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_499])).

tff(c_543,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_514])).

tff(c_1381,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_543])).

tff(c_1579,plain,(
    ! [B_144,C_143,D_145,A_142,E_141,F_140] :
      ( m1_subset_1(k1_partfun1(A_142,B_144,C_143,D_145,E_141,F_140),k1_zfmisc_1(k2_zfmisc_1(A_142,D_145)))
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_143,D_145)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_144)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1613,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_1579])).

tff(c_1634,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_1613])).

tff(c_1636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1381,c_1634])).

tff(c_1637,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_514])).

tff(c_3078,plain,(
    ! [A_205,B_206,C_207,D_208] :
      ( k2_relset_1(A_205,B_206,C_207) = B_206
      | ~ r2_relset_1(B_206,B_206,k1_partfun1(B_206,A_205,A_205,B_206,D_208,C_207),k6_partfun1(B_206))
      | ~ m1_subset_1(D_208,k1_zfmisc_1(k2_zfmisc_1(B_206,A_205)))
      | ~ v1_funct_2(D_208,B_206,A_205)
      | ~ v1_funct_1(D_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206)))
      | ~ v1_funct_2(C_207,A_205,B_206)
      | ~ v1_funct_1(C_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3084,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1637,c_3078])).

tff(c_3088,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_82,c_80,c_78,c_168,c_233,c_3084])).

tff(c_3090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2572,c_3088])).

tff(c_3091,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2545])).

tff(c_3136,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3091])).

tff(c_20,plain,(
    ! [A_14] : v2_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    ! [A_14] : v2_funct_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_4199,plain,(
    ! [E_245,C_248,D_247,A_249,B_246] :
      ( k1_xboole_0 = C_248
      | v2_funct_1(E_245)
      | k2_relset_1(A_249,B_246,D_247) != B_246
      | ~ v2_funct_1(k1_partfun1(A_249,B_246,B_246,C_248,D_247,E_245))
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(B_246,C_248)))
      | ~ v1_funct_2(E_245,B_246,C_248)
      | ~ v1_funct_1(E_245)
      | ~ m1_subset_1(D_247,k1_zfmisc_1(k2_zfmisc_1(A_249,B_246)))
      | ~ v1_funct_2(D_247,A_249,B_246)
      | ~ v1_funct_1(D_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_4201,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1637,c_4199])).

tff(c_4203,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_84,c_70,c_4201])).

tff(c_4205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3136,c_64,c_4203])).

tff(c_4207,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3091])).

tff(c_16,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4206,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3091])).

tff(c_18,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_85,plain,(
    ! [A_14] : v1_relat_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_10)),A_10) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_10)),A_10) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_248,plain,(
    ! [A_82,B_83,C_84] :
      ( k5_relat_1(k5_relat_1(A_82,B_83),C_84) = k5_relat_1(A_82,k5_relat_1(B_83,C_84))
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_274,plain,(
    ! [A_10,C_84] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_10)),k5_relat_1(A_10,C_84)) = k5_relat_1(A_10,C_84)
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_248])).

tff(c_284,plain,(
    ! [A_10,C_84] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_10)),k5_relat_1(A_10,C_84)) = k5_relat_1(A_10,C_84)
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_274])).

tff(c_4211,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4206,c_284])).

tff(c_4218,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_4206,c_4211])).

tff(c_4836,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4218])).

tff(c_4839,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_4836])).

tff(c_4843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_76,c_4839])).

tff(c_4845,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4218])).

tff(c_120,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_108])).

tff(c_226,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_220])).

tff(c_232,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_226])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k5_relat_1(B_12,k6_relat_1(A_11)) = B_12
      | ~ r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_199,plain,(
    ! [B_76,A_77] :
      ( k5_relat_1(B_76,k6_partfun1(A_77)) = B_76
      | ~ r1_tarski(k2_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_207,plain,(
    ! [B_76] :
      ( k5_relat_1(B_76,k6_partfun1(k2_relat_1(B_76))) = B_76
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_237,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_207])).

tff(c_244,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_237])).

tff(c_3092,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2545])).

tff(c_172,plain,(
    ! [A_74] :
      ( k1_relat_1(k2_funct_1(A_74)) = k2_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5304,plain,(
    ! [A_290] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_290)),k2_funct_1(A_290)) = k2_funct_1(A_290)
      | ~ v1_relat_1(k2_funct_1(A_290))
      | ~ v2_funct_1(A_290)
      | ~ v1_funct_1(A_290)
      | ~ v1_relat_1(A_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_87])).

tff(c_5333,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3092,c_5304])).

tff(c_5358,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_76,c_4207,c_4845,c_5333])).

tff(c_2218,plain,(
    ! [C_170,F_167,D_166,A_165,E_168,B_169] :
      ( k1_partfun1(A_165,B_169,C_170,D_166,E_168,F_167) = k5_relat_1(E_168,F_167)
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(C_170,D_166)))
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_165,B_169)))
      | ~ v1_funct_1(E_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2224,plain,(
    ! [A_165,B_169,E_168] :
      ( k1_partfun1(A_165,B_169,'#skF_2','#skF_1',E_168,'#skF_4') = k5_relat_1(E_168,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_165,B_169)))
      | ~ v1_funct_1(E_168) ) ),
    inference(resolution,[status(thm)],[c_72,c_2218])).

tff(c_4264,plain,(
    ! [A_250,B_251,E_252] :
      ( k1_partfun1(A_250,B_251,'#skF_2','#skF_1',E_252,'#skF_4') = k5_relat_1(E_252,'#skF_4')
      | ~ m1_subset_1(E_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_funct_1(E_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2224])).

tff(c_4270,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4264])).

tff(c_4277,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1637,c_4270])).

tff(c_8,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4296,plain,(
    ! [C_9] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_9) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4277,c_8])).

tff(c_4308,plain,(
    ! [C_9] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_9) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_9))
      | ~ v1_relat_1(C_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_121,c_4296])).

tff(c_5364,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5358,c_4308])).

tff(c_5383,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4845,c_244,c_4206,c_5364])).

tff(c_26,plain,(
    ! [A_16] :
      ( k2_funct_1(k2_funct_1(A_16)) = A_16
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5416,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5383,c_26])).

tff(c_5432,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_76,c_4207,c_5416])).

tff(c_5434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:12:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.64/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.31  
% 6.64/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.31  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.64/2.31  
% 6.64/2.31  %Foreground sorts:
% 6.64/2.31  
% 6.64/2.31  
% 6.64/2.31  %Background operators:
% 6.64/2.31  
% 6.64/2.31  
% 6.64/2.31  %Foreground operators:
% 6.64/2.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.64/2.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.64/2.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.64/2.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.64/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.64/2.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.64/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.64/2.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.64/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.64/2.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.64/2.31  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.64/2.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.64/2.31  tff('#skF_2', type, '#skF_2': $i).
% 6.64/2.31  tff('#skF_3', type, '#skF_3': $i).
% 6.64/2.31  tff('#skF_1', type, '#skF_1': $i).
% 6.64/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.64/2.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.64/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.64/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.64/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.64/2.31  tff('#skF_4', type, '#skF_4': $i).
% 6.64/2.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.64/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.64/2.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.64/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.64/2.31  
% 6.64/2.33  tff(f_208, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.64/2.33  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.64/2.33  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.64/2.33  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 6.64/2.33  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.64/2.33  tff(f_99, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.64/2.33  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.64/2.33  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.64/2.33  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.64/2.33  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.64/2.33  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.64/2.33  tff(f_166, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 6.64/2.33  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.64/2.33  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.64/2.33  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.64/2.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.64/2.33  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 6.64/2.33  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.64/2.33  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 6.64/2.33  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_108, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.64/2.33  tff(c_121, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_108])).
% 6.64/2.33  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_64, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_220, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.64/2.33  tff(c_233, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_220])).
% 6.64/2.33  tff(c_2528, plain, (![A_178, C_179, B_180]: (k6_partfun1(A_178)=k5_relat_1(C_179, k2_funct_1(C_179)) | k1_xboole_0=B_180 | ~v2_funct_1(C_179) | k2_relset_1(A_178, B_180, C_179)!=B_180 | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_180))) | ~v1_funct_2(C_179, A_178, B_180) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.64/2.33  tff(c_2534, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_2528])).
% 6.64/2.33  tff(c_2544, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_233, c_2534])).
% 6.64/2.33  tff(c_2545, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_2544])).
% 6.64/2.33  tff(c_2572, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2545])).
% 6.64/2.33  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_44, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.64/2.33  tff(c_36, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.64/2.33  tff(c_83, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 6.64/2.33  tff(c_161, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.64/2.33  tff(c_168, plain, (![A_27]: (r2_relset_1(A_27, A_27, k6_partfun1(A_27), k6_partfun1(A_27)))), inference(resolution, [status(thm)], [c_83, c_161])).
% 6.64/2.33  tff(c_932, plain, (![E_115, A_112, D_113, B_116, C_117, F_114]: (k1_partfun1(A_112, B_116, C_117, D_113, E_115, F_114)=k5_relat_1(E_115, F_114) | ~m1_subset_1(F_114, k1_zfmisc_1(k2_zfmisc_1(C_117, D_113))) | ~v1_funct_1(F_114) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_116))) | ~v1_funct_1(E_115))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.64/2.33  tff(c_938, plain, (![A_112, B_116, E_115]: (k1_partfun1(A_112, B_116, '#skF_2', '#skF_1', E_115, '#skF_4')=k5_relat_1(E_115, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_116))) | ~v1_funct_1(E_115))), inference(resolution, [status(thm)], [c_72, c_932])).
% 6.64/2.33  tff(c_1363, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_2', '#skF_1', E_136, '#skF_4')=k5_relat_1(E_136, '#skF_4') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_938])).
% 6.64/2.33  tff(c_1369, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1363])).
% 6.64/2.33  tff(c_1376, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1369])).
% 6.64/2.33  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_491, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.64/2.33  tff(c_499, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_491])).
% 6.64/2.33  tff(c_514, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_499])).
% 6.64/2.33  tff(c_543, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_514])).
% 6.64/2.33  tff(c_1381, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_543])).
% 6.64/2.33  tff(c_1579, plain, (![B_144, C_143, D_145, A_142, E_141, F_140]: (m1_subset_1(k1_partfun1(A_142, B_144, C_143, D_145, E_141, F_140), k1_zfmisc_1(k2_zfmisc_1(A_142, D_145))) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_143, D_145))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_144))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.64/2.33  tff(c_1613, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1376, c_1579])).
% 6.64/2.33  tff(c_1634, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_1613])).
% 6.64/2.33  tff(c_1636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1381, c_1634])).
% 6.64/2.33  tff(c_1637, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_514])).
% 6.64/2.33  tff(c_3078, plain, (![A_205, B_206, C_207, D_208]: (k2_relset_1(A_205, B_206, C_207)=B_206 | ~r2_relset_1(B_206, B_206, k1_partfun1(B_206, A_205, A_205, B_206, D_208, C_207), k6_partfun1(B_206)) | ~m1_subset_1(D_208, k1_zfmisc_1(k2_zfmisc_1(B_206, A_205))) | ~v1_funct_2(D_208, B_206, A_205) | ~v1_funct_1(D_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))) | ~v1_funct_2(C_207, A_205, B_206) | ~v1_funct_1(C_207))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.64/2.33  tff(c_3084, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1637, c_3078])).
% 6.64/2.33  tff(c_3088, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_82, c_80, c_78, c_168, c_233, c_3084])).
% 6.64/2.33  tff(c_3090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2572, c_3088])).
% 6.64/2.33  tff(c_3091, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2545])).
% 6.64/2.33  tff(c_3136, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3091])).
% 6.64/2.33  tff(c_20, plain, (![A_14]: (v2_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.64/2.33  tff(c_84, plain, (![A_14]: (v2_funct_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 6.64/2.33  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.64/2.33  tff(c_4199, plain, (![E_245, C_248, D_247, A_249, B_246]: (k1_xboole_0=C_248 | v2_funct_1(E_245) | k2_relset_1(A_249, B_246, D_247)!=B_246 | ~v2_funct_1(k1_partfun1(A_249, B_246, B_246, C_248, D_247, E_245)) | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(B_246, C_248))) | ~v1_funct_2(E_245, B_246, C_248) | ~v1_funct_1(E_245) | ~m1_subset_1(D_247, k1_zfmisc_1(k2_zfmisc_1(A_249, B_246))) | ~v1_funct_2(D_247, A_249, B_246) | ~v1_funct_1(D_247))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.64/2.33  tff(c_4201, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1637, c_4199])).
% 6.64/2.33  tff(c_4203, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_84, c_70, c_4201])).
% 6.64/2.33  tff(c_4205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3136, c_64, c_4203])).
% 6.64/2.33  tff(c_4207, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3091])).
% 6.64/2.33  tff(c_16, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.64/2.33  tff(c_4206, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3091])).
% 6.64/2.33  tff(c_18, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.64/2.33  tff(c_85, plain, (![A_14]: (v1_relat_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 6.64/2.33  tff(c_10, plain, (![A_10]: (k5_relat_1(k6_relat_1(k1_relat_1(A_10)), A_10)=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.64/2.33  tff(c_87, plain, (![A_10]: (k5_relat_1(k6_partfun1(k1_relat_1(A_10)), A_10)=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 6.64/2.33  tff(c_248, plain, (![A_82, B_83, C_84]: (k5_relat_1(k5_relat_1(A_82, B_83), C_84)=k5_relat_1(A_82, k5_relat_1(B_83, C_84)) | ~v1_relat_1(C_84) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.64/2.33  tff(c_274, plain, (![A_10, C_84]: (k5_relat_1(k6_partfun1(k1_relat_1(A_10)), k5_relat_1(A_10, C_84))=k5_relat_1(A_10, C_84) | ~v1_relat_1(C_84) | ~v1_relat_1(A_10) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_87, c_248])).
% 6.64/2.33  tff(c_284, plain, (![A_10, C_84]: (k5_relat_1(k6_partfun1(k1_relat_1(A_10)), k5_relat_1(A_10, C_84))=k5_relat_1(A_10, C_84) | ~v1_relat_1(C_84) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_274])).
% 6.64/2.33  tff(c_4211, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4206, c_284])).
% 6.64/2.33  tff(c_4218, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_4206, c_4211])).
% 6.64/2.33  tff(c_4836, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4218])).
% 6.64/2.33  tff(c_4839, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_4836])).
% 6.64/2.33  tff(c_4843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_76, c_4839])).
% 6.64/2.33  tff(c_4845, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4218])).
% 6.64/2.33  tff(c_120, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_108])).
% 6.64/2.33  tff(c_226, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_220])).
% 6.64/2.33  tff(c_232, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_226])).
% 6.64/2.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.64/2.33  tff(c_12, plain, (![B_12, A_11]: (k5_relat_1(B_12, k6_relat_1(A_11))=B_12 | ~r1_tarski(k2_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.64/2.33  tff(c_199, plain, (![B_76, A_77]: (k5_relat_1(B_76, k6_partfun1(A_77))=B_76 | ~r1_tarski(k2_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 6.64/2.33  tff(c_207, plain, (![B_76]: (k5_relat_1(B_76, k6_partfun1(k2_relat_1(B_76)))=B_76 | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_6, c_199])).
% 6.64/2.33  tff(c_237, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_232, c_207])).
% 6.64/2.33  tff(c_244, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_237])).
% 6.64/2.33  tff(c_3092, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2545])).
% 6.64/2.33  tff(c_172, plain, (![A_74]: (k1_relat_1(k2_funct_1(A_74))=k2_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.64/2.33  tff(c_5304, plain, (![A_290]: (k5_relat_1(k6_partfun1(k2_relat_1(A_290)), k2_funct_1(A_290))=k2_funct_1(A_290) | ~v1_relat_1(k2_funct_1(A_290)) | ~v2_funct_1(A_290) | ~v1_funct_1(A_290) | ~v1_relat_1(A_290))), inference(superposition, [status(thm), theory('equality')], [c_172, c_87])).
% 6.64/2.33  tff(c_5333, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3092, c_5304])).
% 6.64/2.33  tff(c_5358, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_76, c_4207, c_4845, c_5333])).
% 6.64/2.33  tff(c_2218, plain, (![C_170, F_167, D_166, A_165, E_168, B_169]: (k1_partfun1(A_165, B_169, C_170, D_166, E_168, F_167)=k5_relat_1(E_168, F_167) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(C_170, D_166))) | ~v1_funct_1(F_167) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_165, B_169))) | ~v1_funct_1(E_168))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.64/2.33  tff(c_2224, plain, (![A_165, B_169, E_168]: (k1_partfun1(A_165, B_169, '#skF_2', '#skF_1', E_168, '#skF_4')=k5_relat_1(E_168, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_165, B_169))) | ~v1_funct_1(E_168))), inference(resolution, [status(thm)], [c_72, c_2218])).
% 6.64/2.33  tff(c_4264, plain, (![A_250, B_251, E_252]: (k1_partfun1(A_250, B_251, '#skF_2', '#skF_1', E_252, '#skF_4')=k5_relat_1(E_252, '#skF_4') | ~m1_subset_1(E_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~v1_funct_1(E_252))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2224])).
% 6.64/2.33  tff(c_4270, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4264])).
% 6.64/2.33  tff(c_4277, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1637, c_4270])).
% 6.64/2.33  tff(c_8, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.64/2.33  tff(c_4296, plain, (![C_9]: (k5_relat_1(k6_partfun1('#skF_1'), C_9)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4277, c_8])).
% 6.64/2.33  tff(c_4308, plain, (![C_9]: (k5_relat_1(k6_partfun1('#skF_1'), C_9)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_9)) | ~v1_relat_1(C_9))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_121, c_4296])).
% 6.64/2.33  tff(c_5364, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5358, c_4308])).
% 6.64/2.33  tff(c_5383, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4845, c_244, c_4206, c_5364])).
% 6.64/2.33  tff(c_26, plain, (![A_16]: (k2_funct_1(k2_funct_1(A_16))=A_16 | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.64/2.33  tff(c_5416, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5383, c_26])).
% 6.64/2.33  tff(c_5432, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_76, c_4207, c_5416])).
% 6.64/2.33  tff(c_5434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_5432])).
% 6.64/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.33  
% 6.64/2.33  Inference rules
% 6.64/2.33  ----------------------
% 6.64/2.33  #Ref     : 0
% 6.64/2.33  #Sup     : 1165
% 6.64/2.33  #Fact    : 0
% 6.64/2.33  #Define  : 0
% 6.64/2.33  #Split   : 14
% 6.64/2.33  #Chain   : 0
% 6.64/2.33  #Close   : 0
% 6.64/2.33  
% 6.64/2.33  Ordering : KBO
% 6.64/2.33  
% 6.64/2.33  Simplification rules
% 6.64/2.33  ----------------------
% 6.64/2.33  #Subsume      : 32
% 6.64/2.33  #Demod        : 1596
% 6.64/2.33  #Tautology    : 587
% 6.64/2.33  #SimpNegUnit  : 39
% 6.64/2.33  #BackRed      : 24
% 6.64/2.33  
% 6.64/2.33  #Partial instantiations: 0
% 6.64/2.33  #Strategies tried      : 1
% 6.64/2.33  
% 6.64/2.33  Timing (in seconds)
% 6.64/2.33  ----------------------
% 6.64/2.34  Preprocessing        : 0.38
% 6.64/2.34  Parsing              : 0.20
% 6.64/2.34  CNF conversion       : 0.03
% 6.64/2.34  Main loop            : 1.17
% 6.64/2.34  Inferencing          : 0.41
% 6.64/2.34  Reduction            : 0.45
% 6.64/2.34  Demodulation         : 0.34
% 6.64/2.34  BG Simplification    : 0.05
% 6.64/2.34  Subsumption          : 0.19
% 6.64/2.34  Abstraction          : 0.06
% 6.64/2.34  MUC search           : 0.00
% 6.64/2.34  Cooper               : 0.00
% 6.64/2.34  Total                : 1.60
% 6.64/2.34  Index Insertion      : 0.00
% 6.64/2.34  Index Deletion       : 0.00
% 6.64/2.34  Index Matching       : 0.00
% 6.64/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
