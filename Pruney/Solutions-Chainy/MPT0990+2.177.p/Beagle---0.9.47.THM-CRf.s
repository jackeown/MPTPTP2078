%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:22 EST 2020

% Result     : Theorem 29.26s
% Output     : CNFRefutation 29.26s
% Verified   : 
% Statistics : Number of formulae       :  196 (1989 expanded)
%              Number of leaves         :   48 ( 715 expanded)
%              Depth                    :   26
%              Number of atoms          :  505 (8349 expanded)
%              Number of equality atoms :  183 (2946 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_193,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_151,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_134,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_94,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_177,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_273,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_296,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_273])).

tff(c_1199,plain,(
    ! [B_214,C_215,A_216] :
      ( k6_partfun1(B_214) = k5_relat_1(k2_funct_1(C_215),C_215)
      | k1_xboole_0 = B_214
      | ~ v2_funct_1(C_215)
      | k2_relset_1(A_216,B_214,C_215) != B_214
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_214)))
      | ~ v1_funct_2(C_215,A_216,B_214)
      | ~ v1_funct_1(C_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1208,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1199])).

tff(c_1222,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_296,c_1208])).

tff(c_1223,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1222])).

tff(c_1235,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_46,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_217,plain,(
    ! [A_79,B_80,D_81] :
      ( r2_relset_1(A_79,B_80,D_81,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_231,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_46,c_217])).

tff(c_602,plain,(
    ! [B_137,F_135,A_133,D_134,E_136,C_138] :
      ( k1_partfun1(A_133,B_137,C_138,D_134,E_136,F_135) = k5_relat_1(E_136,F_135)
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_138,D_134)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_133,B_137)))
      | ~ v1_funct_1(E_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_611,plain,(
    ! [A_133,B_137,E_136] :
      ( k1_partfun1(A_133,B_137,'#skF_2','#skF_1',E_136,'#skF_4') = k5_relat_1(E_136,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_133,B_137)))
      | ~ v1_funct_1(E_136) ) ),
    inference(resolution,[status(thm)],[c_78,c_602])).

tff(c_739,plain,(
    ! [A_154,B_155,E_156] :
      ( k1_partfun1(A_154,B_155,'#skF_2','#skF_1',E_156,'#skF_4') = k5_relat_1(E_156,'#skF_4')
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_1(E_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_611])).

tff(c_749,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_739])).

tff(c_761,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_749])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_438,plain,(
    ! [D_107,C_108,A_109,B_110] :
      ( D_107 = C_108
      | ~ r2_relset_1(A_109,B_110,C_108,D_107)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_448,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_438])).

tff(c_467,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_448])).

tff(c_468,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_768,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_468])).

tff(c_871,plain,(
    ! [A_174,C_170,D_171,B_173,F_169,E_172] :
      ( m1_subset_1(k1_partfun1(A_174,B_173,C_170,D_171,E_172,F_169),k1_zfmisc_1(k2_zfmisc_1(A_174,D_171)))
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_170,D_171)))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173)))
      | ~ v1_funct_1(E_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_908,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_871])).

tff(c_932,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_908])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_768,c_932])).

tff(c_935,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_1843,plain,(
    ! [A_239,B_240,C_241,D_242] :
      ( k2_relset_1(A_239,B_240,C_241) = B_240
      | ~ r2_relset_1(B_240,B_240,k1_partfun1(B_240,A_239,A_239,B_240,D_242,C_241),k6_partfun1(B_240))
      | ~ m1_subset_1(D_242,k1_zfmisc_1(k2_zfmisc_1(B_240,A_239)))
      | ~ v1_funct_2(D_242,B_240,A_239)
      | ~ v1_funct_1(D_242)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240)))
      | ~ v1_funct_2(C_241,A_239,B_240)
      | ~ v1_funct_1(C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1849,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_1843])).

tff(c_1853,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_88,c_86,c_84,c_231,c_296,c_1849])).

tff(c_1855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1235,c_1853])).

tff(c_1857,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_167,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_179,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_167])).

tff(c_192,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_176,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_167])).

tff(c_189,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_283,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_273])).

tff(c_295,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_283])).

tff(c_50,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    ! [A_17,B_19] :
      ( k2_funct_1(A_17) = B_19
      | k6_relat_1(k2_relat_1(A_17)) != k5_relat_1(B_19,A_17)
      | k2_relat_1(B_19) != k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_968,plain,(
    ! [A_178,B_179] :
      ( k2_funct_1(A_178) = B_179
      | k6_partfun1(k2_relat_1(A_178)) != k5_relat_1(B_179,A_178)
      | k2_relat_1(B_179) != k1_relat_1(A_178)
      | ~ v2_funct_1(A_178)
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179)
      | ~ v1_funct_1(A_178)
      | ~ v1_relat_1(A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_32])).

tff(c_978,plain,(
    ! [B_179] :
      ( k2_funct_1('#skF_3') = B_179
      | k5_relat_1(B_179,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_179) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_968])).

tff(c_987,plain,(
    ! [B_180] :
      ( k2_funct_1('#skF_3') = B_180
      | k5_relat_1(B_180,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_180) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_180)
      | ~ v1_relat_1(B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_88,c_72,c_978])).

tff(c_990,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_987])).

tff(c_1005,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_990])).

tff(c_1006,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1005])).

tff(c_1014,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1006])).

tff(c_1858,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_1014])).

tff(c_22,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_141,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_94,c_141])).

tff(c_18,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1927,plain,(
    ! [A_246,C_247,B_248] :
      ( k6_partfun1(A_246) = k5_relat_1(C_247,k2_funct_1(C_247))
      | k1_xboole_0 = B_248
      | ~ v2_funct_1(C_247)
      | k2_relset_1(A_246,B_248,C_247) != B_248
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_246,B_248)))
      | ~ v1_funct_2(C_247,A_246,B_248)
      | ~ v1_funct_1(C_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1934,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1927])).

tff(c_1946,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_1934])).

tff(c_1947,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1946])).

tff(c_30,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_311,plain,(
    ! [B_94,A_95] :
      ( k2_relat_1(k5_relat_1(B_94,A_95)) = k2_relat_1(A_95)
      | ~ r1_tarski(k1_relat_1(A_95),k2_relat_1(B_94))
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_314,plain,(
    ! [A_95] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_95)) = k2_relat_1(A_95)
      | ~ r1_tarski(k1_relat_1(A_95),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_311])).

tff(c_368,plain,(
    ! [A_101] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_101)) = k2_relat_1(A_101)
      | ~ r1_tarski(k1_relat_1(A_101),'#skF_2')
      | ~ v1_relat_1(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_314])).

tff(c_371,plain,(
    ! [A_16] :
      ( k2_relat_1(k5_relat_1('#skF_3',k2_funct_1(A_16))) = k2_relat_1(k2_funct_1(A_16))
      | ~ r1_tarski(k2_relat_1(A_16),'#skF_2')
      | ~ v1_relat_1(k2_funct_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_368])).

tff(c_1957,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1947,c_371])).

tff(c_1961,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_88,c_72,c_157,c_295,c_92,c_1957])).

tff(c_1963,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1961])).

tff(c_1993,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1963])).

tff(c_1997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_88,c_1993])).

tff(c_1998,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1961])).

tff(c_28,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2018,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1998,c_28])).

tff(c_2031,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_88,c_72,c_2018])).

tff(c_2033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1858,c_2031])).

tff(c_2034,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1006])).

tff(c_2130,plain,(
    ! [A_263,E_266,D_264,B_267,F_265,C_268] :
      ( k1_partfun1(A_263,B_267,C_268,D_264,E_266,F_265) = k5_relat_1(E_266,F_265)
      | ~ m1_subset_1(F_265,k1_zfmisc_1(k2_zfmisc_1(C_268,D_264)))
      | ~ v1_funct_1(F_265)
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_263,B_267)))
      | ~ v1_funct_1(E_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2139,plain,(
    ! [A_263,B_267,E_266] :
      ( k1_partfun1(A_263,B_267,'#skF_2','#skF_1',E_266,'#skF_4') = k5_relat_1(E_266,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_263,B_267)))
      | ~ v1_funct_1(E_266) ) ),
    inference(resolution,[status(thm)],[c_78,c_2130])).

tff(c_3632,plain,(
    ! [A_360,B_361,E_362] :
      ( k1_partfun1(A_360,B_361,'#skF_2','#skF_1',E_362,'#skF_4') = k5_relat_1(E_362,'#skF_4')
      | ~ m1_subset_1(E_362,k1_zfmisc_1(k2_zfmisc_1(A_360,B_361)))
      | ~ v1_funct_1(E_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2139])).

tff(c_3657,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3632])).

tff(c_3682,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_935,c_3657])).

tff(c_2035,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1006])).

tff(c_2036,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2035,c_296])).

tff(c_2253,plain,(
    ! [B_284,C_285,A_286] :
      ( k6_partfun1(B_284) = k5_relat_1(k2_funct_1(C_285),C_285)
      | k1_xboole_0 = B_284
      | ~ v2_funct_1(C_285)
      | k2_relset_1(A_286,B_284,C_285) != B_284
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_286,B_284)))
      | ~ v1_funct_2(C_285,A_286,B_284)
      | ~ v1_funct_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_2262,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2253])).

tff(c_2276,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2036,c_2262])).

tff(c_2277,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2276])).

tff(c_2289,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2277])).

tff(c_2339,plain,(
    ! [A_291,C_292,B_293] :
      ( k6_partfun1(A_291) = k5_relat_1(C_292,k2_funct_1(C_292))
      | k1_xboole_0 = B_293
      | ~ v2_funct_1(C_292)
      | k2_relset_1(A_291,B_293,C_292) != B_293
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_291,B_293)))
      | ~ v1_funct_2(C_292,A_291,B_293)
      | ~ v1_funct_1(C_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_2346,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_2339])).

tff(c_2358,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_2346])).

tff(c_2359,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2358])).

tff(c_2369,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2359,c_371])).

tff(c_2373,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_88,c_72,c_157,c_295,c_92,c_2369])).

tff(c_2375,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2373])).

tff(c_2405,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2375])).

tff(c_2409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_88,c_2405])).

tff(c_2410,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2373])).

tff(c_2430,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2410,c_28])).

tff(c_2443,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_88,c_72,c_2430])).

tff(c_2445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2289,c_2443])).

tff(c_2447,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2277])).

tff(c_2451,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2447,c_2036])).

tff(c_2473,plain,(
    ! [A_297,C_298,B_299] :
      ( k6_partfun1(A_297) = k5_relat_1(C_298,k2_funct_1(C_298))
      | k1_xboole_0 = B_299
      | ~ v2_funct_1(C_298)
      | k2_relset_1(A_297,B_299,C_298) != B_299
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_297,B_299)))
      | ~ v1_funct_2(C_298,A_297,B_299)
      | ~ v1_funct_1(C_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_2482,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2473])).

tff(c_2496,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2482])).

tff(c_2497,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2496])).

tff(c_2527,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_2497])).

tff(c_2528,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2527])).

tff(c_26,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_90,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26])).

tff(c_2881,plain,(
    ! [E_318,C_321,A_322,D_320,B_319] :
      ( k1_xboole_0 = C_321
      | v2_funct_1(E_318)
      | k2_relset_1(A_322,B_319,D_320) != B_319
      | ~ v2_funct_1(k1_partfun1(A_322,B_319,B_319,C_321,D_320,E_318))
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(B_319,C_321)))
      | ~ v1_funct_2(E_318,B_319,C_321)
      | ~ v1_funct_1(E_318)
      | ~ m1_subset_1(D_320,k1_zfmisc_1(k2_zfmisc_1(A_322,B_319)))
      | ~ v1_funct_2(D_320,A_322,B_319)
      | ~ v1_funct_1(D_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2885,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_935,c_2881])).

tff(c_2890,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_90,c_76,c_2885])).

tff(c_2892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2528,c_70,c_2890])).

tff(c_2894,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2527])).

tff(c_2893,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2527])).

tff(c_4611,plain,(
    ! [B_401,A_402] :
      ( k2_relat_1(k5_relat_1(B_401,k2_funct_1(A_402))) = k2_relat_1(k2_funct_1(A_402))
      | ~ r1_tarski(k2_relat_1(A_402),k2_relat_1(B_401))
      | ~ v1_relat_1(B_401)
      | ~ v1_relat_1(k2_funct_1(A_402))
      | ~ v2_funct_1(A_402)
      | ~ v1_funct_1(A_402)
      | ~ v1_relat_1(A_402) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_311])).

tff(c_8600,plain,(
    ! [A_527] :
      ( k2_relat_1(k5_relat_1(A_527,k2_funct_1(A_527))) = k2_relat_1(k2_funct_1(A_527))
      | ~ v1_relat_1(k2_funct_1(A_527))
      | ~ v2_funct_1(A_527)
      | ~ v1_funct_1(A_527)
      | ~ v1_relat_1(A_527) ) ),
    inference(resolution,[status(thm)],[c_157,c_4611])).

tff(c_8653,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2893,c_8600])).

tff(c_8684,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_82,c_2894,c_92,c_8653])).

tff(c_8692,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8684])).

tff(c_8695,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_8692])).

tff(c_8699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_82,c_8695])).

tff(c_8700,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8684])).

tff(c_8726,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8700,c_28])).

tff(c_8745,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_82,c_2894,c_8726])).

tff(c_2452,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2447,c_2035])).

tff(c_89,plain,(
    ! [A_17,B_19] :
      ( k2_funct_1(A_17) = B_19
      | k6_partfun1(k2_relat_1(A_17)) != k5_relat_1(B_19,A_17)
      | k2_relat_1(B_19) != k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_32])).

tff(c_2502,plain,(
    ! [B_19] :
      ( k2_funct_1('#skF_4') = B_19
      | k5_relat_1(B_19,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_19) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2452,c_89])).

tff(c_2509,plain,(
    ! [B_19] :
      ( k2_funct_1('#skF_4') = B_19
      | k5_relat_1(B_19,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_19) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_82,c_2502])).

tff(c_38554,plain,(
    ! [B_1150] :
      ( k2_funct_1('#skF_4') = B_1150
      | k5_relat_1(B_1150,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1150) != '#skF_2'
      | ~ v1_funct_1(B_1150)
      | ~ v1_relat_1(B_1150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2894,c_8745,c_2509])).

tff(c_39316,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_189,c_38554])).

tff(c_39942,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_295,c_3682,c_39316])).

tff(c_39953,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39942,c_2893])).

tff(c_39958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2034,c_39953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.26/20.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.26/20.09  
% 29.26/20.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.26/20.09  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 29.26/20.09  
% 29.26/20.09  %Foreground sorts:
% 29.26/20.09  
% 29.26/20.09  
% 29.26/20.09  %Background operators:
% 29.26/20.09  
% 29.26/20.09  
% 29.26/20.09  %Foreground operators:
% 29.26/20.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 29.26/20.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 29.26/20.09  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 29.26/20.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 29.26/20.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.26/20.09  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 29.26/20.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.26/20.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 29.26/20.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.26/20.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.26/20.09  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 29.26/20.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 29.26/20.09  tff('#skF_2', type, '#skF_2': $i).
% 29.26/20.09  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 29.26/20.09  tff('#skF_3', type, '#skF_3': $i).
% 29.26/20.09  tff('#skF_1', type, '#skF_1': $i).
% 29.26/20.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.26/20.09  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 29.26/20.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.26/20.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.26/20.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 29.26/20.09  tff('#skF_4', type, '#skF_4': $i).
% 29.26/20.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 29.26/20.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.26/20.09  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 29.26/20.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.26/20.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.26/20.09  
% 29.26/20.12  tff(f_219, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 29.26/20.12  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 29.26/20.12  tff(f_193, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 29.26/20.12  tff(f_122, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 29.26/20.12  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 29.26/20.12  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 29.26/20.12  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 29.26/20.12  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 29.26/20.12  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 29.26/20.12  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 29.26/20.12  tff(f_134, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 29.26/20.12  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 29.26/20.12  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 29.26/20.12  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 29.26/20.12  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 29.26/20.12  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 29.26/20.12  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 29.26/20.12  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 29.26/20.12  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 29.26/20.12  tff(f_67, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 29.26/20.12  tff(f_177, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 29.26/20.12  tff(c_70, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_273, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 29.26/20.12  tff(c_296, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_273])).
% 29.26/20.12  tff(c_1199, plain, (![B_214, C_215, A_216]: (k6_partfun1(B_214)=k5_relat_1(k2_funct_1(C_215), C_215) | k1_xboole_0=B_214 | ~v2_funct_1(C_215) | k2_relset_1(A_216, B_214, C_215)!=B_214 | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_214))) | ~v1_funct_2(C_215, A_216, B_214) | ~v1_funct_1(C_215))), inference(cnfTransformation, [status(thm)], [f_193])).
% 29.26/20.12  tff(c_1208, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1199])).
% 29.26/20.12  tff(c_1222, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_296, c_1208])).
% 29.26/20.12  tff(c_1223, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_70, c_1222])).
% 29.26/20.12  tff(c_1235, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1223])).
% 29.26/20.12  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_46, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 29.26/20.12  tff(c_217, plain, (![A_79, B_80, D_81]: (r2_relset_1(A_79, B_80, D_81, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 29.26/20.12  tff(c_231, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_46, c_217])).
% 29.26/20.12  tff(c_602, plain, (![B_137, F_135, A_133, D_134, E_136, C_138]: (k1_partfun1(A_133, B_137, C_138, D_134, E_136, F_135)=k5_relat_1(E_136, F_135) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_138, D_134))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_133, B_137))) | ~v1_funct_1(E_136))), inference(cnfTransformation, [status(thm)], [f_132])).
% 29.26/20.12  tff(c_611, plain, (![A_133, B_137, E_136]: (k1_partfun1(A_133, B_137, '#skF_2', '#skF_1', E_136, '#skF_4')=k5_relat_1(E_136, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_133, B_137))) | ~v1_funct_1(E_136))), inference(resolution, [status(thm)], [c_78, c_602])).
% 29.26/20.12  tff(c_739, plain, (![A_154, B_155, E_156]: (k1_partfun1(A_154, B_155, '#skF_2', '#skF_1', E_156, '#skF_4')=k5_relat_1(E_156, '#skF_4') | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_1(E_156))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_611])).
% 29.26/20.12  tff(c_749, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_739])).
% 29.26/20.12  tff(c_761, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_749])).
% 29.26/20.12  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_438, plain, (![D_107, C_108, A_109, B_110]: (D_107=C_108 | ~r2_relset_1(A_109, B_110, C_108, D_107) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 29.26/20.12  tff(c_448, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_438])).
% 29.26/20.12  tff(c_467, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_448])).
% 29.26/20.12  tff(c_468, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_467])).
% 29.26/20.12  tff(c_768, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_761, c_468])).
% 29.26/20.12  tff(c_871, plain, (![A_174, C_170, D_171, B_173, F_169, E_172]: (m1_subset_1(k1_partfun1(A_174, B_173, C_170, D_171, E_172, F_169), k1_zfmisc_1(k2_zfmisc_1(A_174, D_171))) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(C_170, D_171))) | ~v1_funct_1(F_169) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))) | ~v1_funct_1(E_172))), inference(cnfTransformation, [status(thm)], [f_118])).
% 29.26/20.12  tff(c_908, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_761, c_871])).
% 29.26/20.12  tff(c_932, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_908])).
% 29.26/20.12  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_768, c_932])).
% 29.26/20.12  tff(c_935, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_467])).
% 29.26/20.12  tff(c_1843, plain, (![A_239, B_240, C_241, D_242]: (k2_relset_1(A_239, B_240, C_241)=B_240 | ~r2_relset_1(B_240, B_240, k1_partfun1(B_240, A_239, A_239, B_240, D_242, C_241), k6_partfun1(B_240)) | ~m1_subset_1(D_242, k1_zfmisc_1(k2_zfmisc_1(B_240, A_239))) | ~v1_funct_2(D_242, B_240, A_239) | ~v1_funct_1(D_242) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))) | ~v1_funct_2(C_241, A_239, B_240) | ~v1_funct_1(C_241))), inference(cnfTransformation, [status(thm)], [f_151])).
% 29.26/20.12  tff(c_1849, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_935, c_1843])).
% 29.26/20.12  tff(c_1853, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_88, c_86, c_84, c_231, c_296, c_1849])).
% 29.26/20.12  tff(c_1855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1235, c_1853])).
% 29.26/20.12  tff(c_1857, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1223])).
% 29.26/20.12  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 29.26/20.12  tff(c_167, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_40])).
% 29.26/20.12  tff(c_179, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_167])).
% 29.26/20.12  tff(c_192, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 29.26/20.12  tff(c_176, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_167])).
% 29.26/20.12  tff(c_189, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_176])).
% 29.26/20.12  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_283, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_273])).
% 29.26/20.12  tff(c_295, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_283])).
% 29.26/20.12  tff(c_50, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_134])).
% 29.26/20.12  tff(c_32, plain, (![A_17, B_19]: (k2_funct_1(A_17)=B_19 | k6_relat_1(k2_relat_1(A_17))!=k5_relat_1(B_19, A_17) | k2_relat_1(B_19)!=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_94])).
% 29.26/20.12  tff(c_968, plain, (![A_178, B_179]: (k2_funct_1(A_178)=B_179 | k6_partfun1(k2_relat_1(A_178))!=k5_relat_1(B_179, A_178) | k2_relat_1(B_179)!=k1_relat_1(A_178) | ~v2_funct_1(A_178) | ~v1_funct_1(B_179) | ~v1_relat_1(B_179) | ~v1_funct_1(A_178) | ~v1_relat_1(A_178))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_32])).
% 29.26/20.12  tff(c_978, plain, (![B_179]: (k2_funct_1('#skF_3')=B_179 | k5_relat_1(B_179, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_179)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_179) | ~v1_relat_1(B_179) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_968])).
% 29.26/20.12  tff(c_987, plain, (![B_180]: (k2_funct_1('#skF_3')=B_180 | k5_relat_1(B_180, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_180)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_180) | ~v1_relat_1(B_180))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_88, c_72, c_978])).
% 29.26/20.12  tff(c_990, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_192, c_987])).
% 29.26/20.12  tff(c_1005, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_990])).
% 29.26/20.12  tff(c_1006, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_1005])).
% 29.26/20.12  tff(c_1014, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1006])).
% 29.26/20.12  tff(c_1858, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1857, c_1014])).
% 29.26/20.12  tff(c_22, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 29.26/20.12  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.26/20.12  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.26/20.12  tff(c_94, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 29.26/20.12  tff(c_141, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.26/20.12  tff(c_157, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_94, c_141])).
% 29.26/20.12  tff(c_18, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 29.26/20.12  tff(c_92, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 29.26/20.12  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_219])).
% 29.26/20.12  tff(c_1927, plain, (![A_246, C_247, B_248]: (k6_partfun1(A_246)=k5_relat_1(C_247, k2_funct_1(C_247)) | k1_xboole_0=B_248 | ~v2_funct_1(C_247) | k2_relset_1(A_246, B_248, C_247)!=B_248 | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_246, B_248))) | ~v1_funct_2(C_247, A_246, B_248) | ~v1_funct_1(C_247))), inference(cnfTransformation, [status(thm)], [f_193])).
% 29.26/20.12  tff(c_1934, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1927])).
% 29.26/20.12  tff(c_1946, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_1934])).
% 29.26/20.12  tff(c_1947, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_1946])).
% 29.26/20.12  tff(c_30, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 29.26/20.12  tff(c_311, plain, (![B_94, A_95]: (k2_relat_1(k5_relat_1(B_94, A_95))=k2_relat_1(A_95) | ~r1_tarski(k1_relat_1(A_95), k2_relat_1(B_94)) | ~v1_relat_1(B_94) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_51])).
% 29.26/20.12  tff(c_314, plain, (![A_95]: (k2_relat_1(k5_relat_1('#skF_3', A_95))=k2_relat_1(A_95) | ~r1_tarski(k1_relat_1(A_95), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_95))), inference(superposition, [status(thm), theory('equality')], [c_295, c_311])).
% 29.26/20.12  tff(c_368, plain, (![A_101]: (k2_relat_1(k5_relat_1('#skF_3', A_101))=k2_relat_1(A_101) | ~r1_tarski(k1_relat_1(A_101), '#skF_2') | ~v1_relat_1(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_314])).
% 29.26/20.12  tff(c_371, plain, (![A_16]: (k2_relat_1(k5_relat_1('#skF_3', k2_funct_1(A_16)))=k2_relat_1(k2_funct_1(A_16)) | ~r1_tarski(k2_relat_1(A_16), '#skF_2') | ~v1_relat_1(k2_funct_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_30, c_368])).
% 29.26/20.12  tff(c_1957, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1947, c_371])).
% 29.26/20.12  tff(c_1961, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_88, c_72, c_157, c_295, c_92, c_1957])).
% 29.26/20.12  tff(c_1963, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1961])).
% 29.26/20.12  tff(c_1993, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_1963])).
% 29.26/20.12  tff(c_1997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_88, c_1993])).
% 29.26/20.12  tff(c_1998, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_1961])).
% 29.26/20.12  tff(c_28, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 29.26/20.12  tff(c_2018, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1998, c_28])).
% 29.26/20.12  tff(c_2031, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_88, c_72, c_2018])).
% 29.26/20.12  tff(c_2033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1858, c_2031])).
% 29.26/20.12  tff(c_2034, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1006])).
% 29.26/20.12  tff(c_2130, plain, (![A_263, E_266, D_264, B_267, F_265, C_268]: (k1_partfun1(A_263, B_267, C_268, D_264, E_266, F_265)=k5_relat_1(E_266, F_265) | ~m1_subset_1(F_265, k1_zfmisc_1(k2_zfmisc_1(C_268, D_264))) | ~v1_funct_1(F_265) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_263, B_267))) | ~v1_funct_1(E_266))), inference(cnfTransformation, [status(thm)], [f_132])).
% 29.26/20.12  tff(c_2139, plain, (![A_263, B_267, E_266]: (k1_partfun1(A_263, B_267, '#skF_2', '#skF_1', E_266, '#skF_4')=k5_relat_1(E_266, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_263, B_267))) | ~v1_funct_1(E_266))), inference(resolution, [status(thm)], [c_78, c_2130])).
% 29.26/20.12  tff(c_3632, plain, (![A_360, B_361, E_362]: (k1_partfun1(A_360, B_361, '#skF_2', '#skF_1', E_362, '#skF_4')=k5_relat_1(E_362, '#skF_4') | ~m1_subset_1(E_362, k1_zfmisc_1(k2_zfmisc_1(A_360, B_361))) | ~v1_funct_1(E_362))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2139])).
% 29.26/20.12  tff(c_3657, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3632])).
% 29.26/20.12  tff(c_3682, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_935, c_3657])).
% 29.26/20.12  tff(c_2035, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1006])).
% 29.26/20.12  tff(c_2036, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2035, c_296])).
% 29.26/20.12  tff(c_2253, plain, (![B_284, C_285, A_286]: (k6_partfun1(B_284)=k5_relat_1(k2_funct_1(C_285), C_285) | k1_xboole_0=B_284 | ~v2_funct_1(C_285) | k2_relset_1(A_286, B_284, C_285)!=B_284 | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_286, B_284))) | ~v1_funct_2(C_285, A_286, B_284) | ~v1_funct_1(C_285))), inference(cnfTransformation, [status(thm)], [f_193])).
% 29.26/20.12  tff(c_2262, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2253])).
% 29.26/20.12  tff(c_2276, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2036, c_2262])).
% 29.26/20.12  tff(c_2277, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_70, c_2276])).
% 29.26/20.12  tff(c_2289, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2277])).
% 29.26/20.12  tff(c_2339, plain, (![A_291, C_292, B_293]: (k6_partfun1(A_291)=k5_relat_1(C_292, k2_funct_1(C_292)) | k1_xboole_0=B_293 | ~v2_funct_1(C_292) | k2_relset_1(A_291, B_293, C_292)!=B_293 | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_291, B_293))) | ~v1_funct_2(C_292, A_291, B_293) | ~v1_funct_1(C_292))), inference(cnfTransformation, [status(thm)], [f_193])).
% 29.26/20.12  tff(c_2346, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_2339])).
% 29.26/20.12  tff(c_2358, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_2346])).
% 29.26/20.12  tff(c_2359, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_2358])).
% 29.26/20.12  tff(c_2369, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2359, c_371])).
% 29.26/20.12  tff(c_2373, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_88, c_72, c_157, c_295, c_92, c_2369])).
% 29.26/20.12  tff(c_2375, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2373])).
% 29.26/20.12  tff(c_2405, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_2375])).
% 29.26/20.12  tff(c_2409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_88, c_2405])).
% 29.26/20.12  tff(c_2410, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_2373])).
% 29.26/20.12  tff(c_2430, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2410, c_28])).
% 29.26/20.12  tff(c_2443, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_88, c_72, c_2430])).
% 29.26/20.12  tff(c_2445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2289, c_2443])).
% 29.26/20.12  tff(c_2447, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2277])).
% 29.26/20.12  tff(c_2451, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2447, c_2036])).
% 29.26/20.12  tff(c_2473, plain, (![A_297, C_298, B_299]: (k6_partfun1(A_297)=k5_relat_1(C_298, k2_funct_1(C_298)) | k1_xboole_0=B_299 | ~v2_funct_1(C_298) | k2_relset_1(A_297, B_299, C_298)!=B_299 | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_297, B_299))) | ~v1_funct_2(C_298, A_297, B_299) | ~v1_funct_1(C_298))), inference(cnfTransformation, [status(thm)], [f_193])).
% 29.26/20.12  tff(c_2482, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2473])).
% 29.26/20.12  tff(c_2496, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2482])).
% 29.26/20.12  tff(c_2497, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_70, c_2496])).
% 29.26/20.12  tff(c_2527, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_2497])).
% 29.26/20.12  tff(c_2528, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2527])).
% 29.26/20.12  tff(c_26, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 29.26/20.12  tff(c_90, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26])).
% 29.26/20.12  tff(c_2881, plain, (![E_318, C_321, A_322, D_320, B_319]: (k1_xboole_0=C_321 | v2_funct_1(E_318) | k2_relset_1(A_322, B_319, D_320)!=B_319 | ~v2_funct_1(k1_partfun1(A_322, B_319, B_319, C_321, D_320, E_318)) | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(B_319, C_321))) | ~v1_funct_2(E_318, B_319, C_321) | ~v1_funct_1(E_318) | ~m1_subset_1(D_320, k1_zfmisc_1(k2_zfmisc_1(A_322, B_319))) | ~v1_funct_2(D_320, A_322, B_319) | ~v1_funct_1(D_320))), inference(cnfTransformation, [status(thm)], [f_177])).
% 29.26/20.12  tff(c_2885, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_935, c_2881])).
% 29.26/20.12  tff(c_2890, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_90, c_76, c_2885])).
% 29.26/20.12  tff(c_2892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2528, c_70, c_2890])).
% 29.26/20.12  tff(c_2894, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2527])).
% 29.26/20.12  tff(c_2893, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2527])).
% 29.26/20.12  tff(c_4611, plain, (![B_401, A_402]: (k2_relat_1(k5_relat_1(B_401, k2_funct_1(A_402)))=k2_relat_1(k2_funct_1(A_402)) | ~r1_tarski(k2_relat_1(A_402), k2_relat_1(B_401)) | ~v1_relat_1(B_401) | ~v1_relat_1(k2_funct_1(A_402)) | ~v2_funct_1(A_402) | ~v1_funct_1(A_402) | ~v1_relat_1(A_402))), inference(superposition, [status(thm), theory('equality')], [c_30, c_311])).
% 29.26/20.12  tff(c_8600, plain, (![A_527]: (k2_relat_1(k5_relat_1(A_527, k2_funct_1(A_527)))=k2_relat_1(k2_funct_1(A_527)) | ~v1_relat_1(k2_funct_1(A_527)) | ~v2_funct_1(A_527) | ~v1_funct_1(A_527) | ~v1_relat_1(A_527))), inference(resolution, [status(thm)], [c_157, c_4611])).
% 29.26/20.12  tff(c_8653, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2893, c_8600])).
% 29.26/20.12  tff(c_8684, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_82, c_2894, c_92, c_8653])).
% 29.26/20.12  tff(c_8692, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8684])).
% 29.26/20.12  tff(c_8695, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_8692])).
% 29.26/20.12  tff(c_8699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_82, c_8695])).
% 29.26/20.12  tff(c_8700, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_8684])).
% 29.26/20.12  tff(c_8726, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8700, c_28])).
% 29.26/20.12  tff(c_8745, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_82, c_2894, c_8726])).
% 29.26/20.12  tff(c_2452, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2447, c_2035])).
% 29.26/20.12  tff(c_89, plain, (![A_17, B_19]: (k2_funct_1(A_17)=B_19 | k6_partfun1(k2_relat_1(A_17))!=k5_relat_1(B_19, A_17) | k2_relat_1(B_19)!=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_32])).
% 29.26/20.12  tff(c_2502, plain, (![B_19]: (k2_funct_1('#skF_4')=B_19 | k5_relat_1(B_19, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_19)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2452, c_89])).
% 29.26/20.12  tff(c_2509, plain, (![B_19]: (k2_funct_1('#skF_4')=B_19 | k5_relat_1(B_19, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_19)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_82, c_2502])).
% 29.26/20.12  tff(c_38554, plain, (![B_1150]: (k2_funct_1('#skF_4')=B_1150 | k5_relat_1(B_1150, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1150)!='#skF_2' | ~v1_funct_1(B_1150) | ~v1_relat_1(B_1150))), inference(demodulation, [status(thm), theory('equality')], [c_2894, c_8745, c_2509])).
% 29.26/20.12  tff(c_39316, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_189, c_38554])).
% 29.26/20.12  tff(c_39942, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_295, c_3682, c_39316])).
% 29.26/20.12  tff(c_39953, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_39942, c_2893])).
% 29.26/20.12  tff(c_39958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2034, c_39953])).
% 29.26/20.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.26/20.12  
% 29.26/20.12  Inference rules
% 29.26/20.12  ----------------------
% 29.26/20.12  #Ref     : 0
% 29.26/20.12  #Sup     : 7855
% 29.26/20.12  #Fact    : 0
% 29.26/20.12  #Define  : 0
% 29.26/20.12  #Split   : 73
% 29.26/20.12  #Chain   : 0
% 29.26/20.12  #Close   : 0
% 29.26/20.12  
% 29.26/20.12  Ordering : KBO
% 29.26/20.12  
% 29.26/20.12  Simplification rules
% 29.26/20.12  ----------------------
% 29.26/20.12  #Subsume      : 478
% 29.26/20.12  #Demod        : 17573
% 29.26/20.12  #Tautology    : 1522
% 29.26/20.12  #SimpNegUnit  : 584
% 29.26/20.12  #BackRed      : 81
% 29.26/20.12  
% 29.26/20.12  #Partial instantiations: 0
% 29.26/20.12  #Strategies tried      : 1
% 29.26/20.12  
% 29.26/20.12  Timing (in seconds)
% 29.26/20.12  ----------------------
% 29.26/20.13  Preprocessing        : 0.39
% 29.26/20.13  Parsing              : 0.20
% 29.26/20.13  CNF conversion       : 0.03
% 29.26/20.13  Main loop            : 18.94
% 29.26/20.13  Inferencing          : 2.96
% 29.26/20.13  Reduction            : 11.50
% 29.26/20.13  Demodulation         : 10.24
% 29.26/20.13  BG Simplification    : 0.19
% 29.26/20.13  Subsumption          : 3.65
% 29.26/20.13  Abstraction          : 0.37
% 29.26/20.13  MUC search           : 0.00
% 29.26/20.13  Cooper               : 0.00
% 29.26/20.13  Total                : 19.40
% 29.26/20.13  Index Insertion      : 0.00
% 29.26/20.13  Index Deletion       : 0.00
% 29.26/20.13  Index Matching       : 0.00
% 29.26/20.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
