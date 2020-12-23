%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:04 EST 2020

% Result     : Theorem 9.90s
% Output     : CNFRefutation 10.00s
% Verified   : 
% Statistics : Number of formulae       :  203 (2104 expanded)
%              Number of leaves         :   57 ( 758 expanded)
%              Depth                    :   21
%              Number of atoms          :  462 (7362 expanded)
%              Number of equality atoms :  156 (2760 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_250,negated_conjecture,(
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

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_165,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_32,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_224,axiom,(
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

tff(f_153,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_182,axiom,(
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

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_101,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_208,axiom,(
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

tff(f_163,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_82,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_100,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_220,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_241,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_220])).

tff(c_104,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_34,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_88,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_66,plain,(
    ! [A_52] : k6_relat_1(A_52) = k6_partfun1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_26,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_110,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_46,plain,(
    ! [A_28] :
      ( k5_relat_1(A_28,k2_funct_1(A_28)) = k6_relat_1(k1_relat_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1029,plain,(
    ! [A_143] :
      ( k5_relat_1(A_143,k2_funct_1(A_143)) = k6_partfun1(k1_relat_1(A_143))
      | ~ v2_funct_1(A_143)
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46])).

tff(c_92,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_454,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_467,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_454])).

tff(c_477,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_467])).

tff(c_510,plain,(
    ! [B_120,A_121] :
      ( k9_relat_1(B_120,k2_relat_1(A_121)) = k2_relat_1(k5_relat_1(A_121,B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_519,plain,(
    ! [B_120] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_120)) = k9_relat_1(B_120,'#skF_3')
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_510])).

tff(c_529,plain,(
    ! [B_120] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_120)) = k9_relat_1(B_120,'#skF_3')
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_519])).

tff(c_1048,plain,
    ( k2_relat_1(k6_partfun1(k1_relat_1('#skF_4'))) = k9_relat_1(k2_funct_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_529])).

tff(c_1060,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_104,c_88,c_110,c_1048])).

tff(c_1062,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1060])).

tff(c_1139,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1062])).

tff(c_1143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_104,c_1139])).

tff(c_1145,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_94,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_240,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_220])).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_70] :
      ( k1_xboole_0 = A_70
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_131,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_140,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_86])).

tff(c_98,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_96,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_475,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_454])).

tff(c_78,plain,(
    ! [B_65,C_66,A_64] :
      ( k6_partfun1(B_65) = k5_relat_1(k2_funct_1(C_66),C_66)
      | k1_xboole_0 = B_65
      | ~ v2_funct_1(C_66)
      | k2_relset_1(A_64,B_65,C_66) != B_65
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2(C_66,A_64,B_65)
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_9156,plain,(
    ! [B_419,C_420,A_421] :
      ( k6_partfun1(B_419) = k5_relat_1(k2_funct_1(C_420),C_420)
      | B_419 = '#skF_1'
      | ~ v2_funct_1(C_420)
      | k2_relset_1(A_421,B_419,C_420) != B_419
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(A_421,B_419)))
      | ~ v1_funct_2(C_420,A_421,B_419)
      | ~ v1_funct_1(C_420) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78])).

tff(c_9163,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_9156])).

tff(c_9175,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_475,c_9163])).

tff(c_9176,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_9175])).

tff(c_9209,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9176])).

tff(c_102,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_62,plain,(
    ! [A_45] : m1_subset_1(k6_partfun1(A_45),k1_zfmisc_1(k2_zfmisc_1(A_45,A_45))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_313,plain,(
    ! [A_101,B_102,D_103] :
      ( r2_relset_1(A_101,B_102,D_103,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_326,plain,(
    ! [A_45] : r2_relset_1(A_45,A_45,k6_partfun1(A_45),k6_partfun1(A_45)) ),
    inference(resolution,[status(thm)],[c_62,c_313])).

tff(c_8284,plain,(
    ! [B_386,A_385,D_388,E_390,C_387,F_389] :
      ( m1_subset_1(k1_partfun1(A_385,B_386,C_387,D_388,E_390,F_389),k1_zfmisc_1(k2_zfmisc_1(A_385,D_388)))
      | ~ m1_subset_1(F_389,k1_zfmisc_1(k2_zfmisc_1(C_387,D_388)))
      | ~ v1_funct_1(F_389)
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386)))
      | ~ v1_funct_1(E_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_90,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_7494,plain,(
    ! [D_351,C_352,A_353,B_354] :
      ( D_351 = C_352
      | ~ r2_relset_1(A_353,B_354,C_352,D_351)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354)))
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_7504,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_90,c_7494])).

tff(c_7523,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7504])).

tff(c_7585,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7523])).

tff(c_8301,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8284,c_7585])).

tff(c_8322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_100,c_98,c_94,c_8301])).

tff(c_8323,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7523])).

tff(c_9903,plain,(
    ! [A_445,B_446,C_447,D_448] :
      ( k2_relset_1(A_445,B_446,C_447) = B_446
      | ~ r2_relset_1(B_446,B_446,k1_partfun1(B_446,A_445,A_445,B_446,D_448,C_447),k6_partfun1(B_446))
      | ~ m1_subset_1(D_448,k1_zfmisc_1(k2_zfmisc_1(B_446,A_445)))
      | ~ v1_funct_2(D_448,B_446,A_445)
      | ~ v1_funct_1(D_448)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446)))
      | ~ v1_funct_2(C_447,A_445,B_446)
      | ~ v1_funct_1(C_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_9909,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8323,c_9903])).

tff(c_9913,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_104,c_102,c_100,c_326,c_475,c_9909])).

tff(c_9915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9209,c_9913])).

tff(c_9917,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9176])).

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_112,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_194,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,B_82)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_210,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_112,c_194])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k5_relat_1(B_22,k6_relat_1(A_21)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_351,plain,(
    ! [B_110,A_111] :
      ( k5_relat_1(B_110,k6_partfun1(A_111)) = B_110
      | ~ r1_tarski(k2_relat_1(B_110),A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_30])).

tff(c_359,plain,(
    ! [B_110] :
      ( k5_relat_1(B_110,k6_partfun1(k2_relat_1(B_110))) = B_110
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_210,c_351])).

tff(c_9928,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9917,c_359])).

tff(c_9942,plain,(
    k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_9928])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_139,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_84])).

tff(c_238,plain,(
    ! [A_45] : v1_relat_1(k6_partfun1(A_45)) ),
    inference(resolution,[status(thm)],[c_62,c_220])).

tff(c_24,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_111,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24])).

tff(c_28,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_290,plain,(
    ! [A_99] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_99)),A_99) = A_99
      | ~ v1_relat_1(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28])).

tff(c_299,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_290])).

tff(c_303,plain,(
    ! [A_19] : k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_299])).

tff(c_105,plain,(
    ! [A_28] :
      ( k5_relat_1(A_28,k2_funct_1(A_28)) = k6_partfun1(k1_relat_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46])).

tff(c_482,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_359])).

tff(c_492,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_482])).

tff(c_109,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28])).

tff(c_1213,plain,(
    ! [A_148,B_149,C_150] :
      ( k5_relat_1(k5_relat_1(A_148,B_149),C_150) = k5_relat_1(A_148,k5_relat_1(B_149,C_150))
      | ~ v1_relat_1(C_150)
      | ~ v1_relat_1(B_149)
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1279,plain,(
    ! [A_20,C_150] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_20)),k5_relat_1(A_20,C_150)) = k5_relat_1(A_20,C_150)
      | ~ v1_relat_1(C_150)
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_20)))
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_1213])).

tff(c_8575,plain,(
    ! [A_400,C_401] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_400)),k5_relat_1(A_400,C_401)) = k5_relat_1(A_400,C_401)
      | ~ v1_relat_1(C_401)
      | ~ v1_relat_1(A_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_1279])).

tff(c_8629,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_8575])).

tff(c_8673,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_238,c_492,c_8629])).

tff(c_22,plain,(
    ! [A_12,B_16,C_18] :
      ( k5_relat_1(k5_relat_1(A_12,B_16),C_18) = k5_relat_1(A_12,k5_relat_1(B_16,C_18))
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8693,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k5_relat_1('#skF_4',C_18)) = k5_relat_1('#skF_4',C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8673,c_22])).

tff(c_8854,plain,(
    ! [C_413] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k5_relat_1('#skF_4',C_413)) = k5_relat_1('#skF_4',C_413)
      | ~ v1_relat_1(C_413) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_241,c_8693])).

tff(c_8895,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1(k1_relat_1('#skF_4'))) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_8854])).

tff(c_8924,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_104,c_88,c_1145,c_303,c_8895])).

tff(c_80,plain,(
    ! [A_64,C_66,B_65] :
      ( k6_partfun1(A_64) = k5_relat_1(C_66,k2_funct_1(C_66))
      | k1_xboole_0 = B_65
      | ~ v2_funct_1(C_66)
      | k2_relset_1(A_64,B_65,C_66) != B_65
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2(C_66,A_64,B_65)
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_10116,plain,(
    ! [A_452,C_453,B_454] :
      ( k6_partfun1(A_452) = k5_relat_1(C_453,k2_funct_1(C_453))
      | B_454 = '#skF_1'
      | ~ v2_funct_1(C_453)
      | k2_relset_1(A_452,B_454,C_453) != B_454
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(A_452,B_454)))
      | ~ v1_funct_2(C_453,A_452,B_454)
      | ~ v1_funct_1(C_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_80])).

tff(c_10125,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_10116])).

tff(c_10139,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_92,c_88,c_8924,c_10125])).

tff(c_10140,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_10139])).

tff(c_10144,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10140,c_8924])).

tff(c_9918,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9917,c_475])).

tff(c_10123,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_10116])).

tff(c_10135,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_9918,c_10123])).

tff(c_10136,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_10135])).

tff(c_10285,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10136])).

tff(c_38,plain,(
    ! [A_26] : v2_funct_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_107,plain,(
    ! [A_26] : v2_funct_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_38])).

tff(c_72,plain,(
    ! [B_59,A_58,D_61,E_63,C_60] :
      ( k1_xboole_0 = C_60
      | v2_funct_1(E_63)
      | k2_relset_1(A_58,B_59,D_61) != B_59
      | ~ v2_funct_1(k1_partfun1(A_58,B_59,B_59,C_60,D_61,E_63))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(B_59,C_60)))
      | ~ v1_funct_2(E_63,B_59,C_60)
      | ~ v1_funct_1(E_63)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(D_61,A_58,B_59)
      | ~ v1_funct_1(D_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_10800,plain,(
    ! [C_482,B_478,D_479,A_480,E_481] :
      ( C_482 = '#skF_1'
      | v2_funct_1(E_481)
      | k2_relset_1(A_480,B_478,D_479) != B_478
      | ~ v2_funct_1(k1_partfun1(A_480,B_478,B_478,C_482,D_479,E_481))
      | ~ m1_subset_1(E_481,k1_zfmisc_1(k2_zfmisc_1(B_478,C_482)))
      | ~ v1_funct_2(E_481,B_478,C_482)
      | ~ v1_funct_1(E_481)
      | ~ m1_subset_1(D_479,k1_zfmisc_1(k2_zfmisc_1(A_480,B_478)))
      | ~ v1_funct_2(D_479,A_480,B_478)
      | ~ v1_funct_1(D_479) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_72])).

tff(c_10804,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8323,c_10800])).

tff(c_10809,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_98,c_96,c_94,c_107,c_92,c_10804])).

tff(c_10811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10285,c_140,c_10809])).

tff(c_10813,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_10136])).

tff(c_10812,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_10136])).

tff(c_18,plain,(
    ! [B_10,A_8] :
      ( k9_relat_1(B_10,k2_relat_1(A_8)) = k2_relat_1(k5_relat_1(A_8,B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_9925,plain,(
    ! [B_10] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_10)) = k9_relat_1(B_10,'#skF_2')
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9917,c_18])).

tff(c_11617,plain,(
    ! [B_515] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_515)) = k9_relat_1(B_515,'#skF_2')
      | ~ v1_relat_1(B_515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_9925])).

tff(c_11652,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_2') = k2_relat_1(k6_partfun1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10812,c_11617])).

tff(c_11680,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_2') = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_11652])).

tff(c_11691,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_11680])).

tff(c_11756,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_11691])).

tff(c_11760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_98,c_11756])).

tff(c_11762,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_11680])).

tff(c_8764,plain,(
    ! [C_410,E_409,F_407,D_408,A_411,B_406] :
      ( k1_partfun1(A_411,B_406,C_410,D_408,E_409,F_407) = k5_relat_1(E_409,F_407)
      | ~ m1_subset_1(F_407,k1_zfmisc_1(k2_zfmisc_1(C_410,D_408)))
      | ~ v1_funct_1(F_407)
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(A_411,B_406)))
      | ~ v1_funct_1(E_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_8771,plain,(
    ! [A_411,B_406,E_409] :
      ( k1_partfun1(A_411,B_406,'#skF_3','#skF_2',E_409,'#skF_5') = k5_relat_1(E_409,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(A_411,B_406)))
      | ~ v1_funct_1(E_409) ) ),
    inference(resolution,[status(thm)],[c_94,c_8764])).

tff(c_9971,plain,(
    ! [A_449,B_450,E_451] :
      ( k1_partfun1(A_449,B_450,'#skF_3','#skF_2',E_451,'#skF_5') = k5_relat_1(E_451,'#skF_5')
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ v1_funct_1(E_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8771])).

tff(c_9984,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_9971])).

tff(c_9996,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_8323,c_9984])).

tff(c_10010,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_18) = k5_relat_1('#skF_4',k5_relat_1('#skF_5',C_18))
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9996,c_22])).

tff(c_13114,plain,(
    ! [C_535] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_535) = k5_relat_1('#skF_4',k5_relat_1('#skF_5',C_535))
      | ~ v1_relat_1(C_535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_240,c_10010])).

tff(c_442,plain,(
    ! [A_116] :
      ( k1_relat_1(k2_funct_1(A_116)) = k2_relat_1(A_116)
      | ~ v2_funct_1(A_116)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_11841,plain,(
    ! [A_517] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_517)),k2_funct_1(A_517)) = k2_funct_1(A_517)
      | ~ v1_relat_1(k2_funct_1(A_517))
      | ~ v2_funct_1(A_517)
      | ~ v1_funct_1(A_517)
      | ~ v1_relat_1(A_517) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_109])).

tff(c_11865,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9917,c_11841])).

tff(c_11898,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_98,c_10813,c_11762,c_11865])).

tff(c_13124,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_5',k2_funct_1('#skF_5'))) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13114,c_11898])).

tff(c_13201,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11762,c_492,c_10812,c_13124])).

tff(c_10971,plain,
    ( k6_partfun1(k1_relat_1('#skF_5')) = k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10812,c_105])).

tff(c_10982,plain,(
    k6_partfun1(k1_relat_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_98,c_10813,c_10971])).

tff(c_11061,plain,(
    k1_relat_1(k6_partfun1('#skF_3')) = k1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10982,c_111])).

tff(c_11093,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_11061])).

tff(c_14874,plain,(
    ! [A_584,C_585] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_584)),C_585) = k5_relat_1(A_584,k5_relat_1(k2_funct_1(A_584),C_585))
      | ~ v1_relat_1(C_585)
      | ~ v1_relat_1(k2_funct_1(A_584))
      | ~ v1_relat_1(A_584)
      | ~ v2_funct_1(A_584)
      | ~ v1_funct_1(A_584)
      | ~ v1_relat_1(A_584) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_1213])).

tff(c_15056,plain,(
    ! [C_585] :
      ( k5_relat_1('#skF_5',k5_relat_1(k2_funct_1('#skF_5'),C_585)) = k5_relat_1(k6_partfun1('#skF_3'),C_585)
      | ~ v1_relat_1(C_585)
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11093,c_14874])).

tff(c_15251,plain,(
    ! [C_586] :
      ( k5_relat_1(k6_partfun1('#skF_3'),C_586) = k5_relat_1('#skF_5',k5_relat_1('#skF_4',C_586))
      | ~ v1_relat_1(C_586) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_98,c_10813,c_240,c_241,c_13201,c_13201,c_15056])).

tff(c_11883,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_11841])).

tff(c_11900,plain,(
    k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_104,c_88,c_1145,c_11883])).

tff(c_15275,plain,
    ( k5_relat_1('#skF_5',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15251,c_11900])).

tff(c_15371,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_9942,c_10144,c_15275])).

tff(c_15373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_15371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:39:05 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.90/3.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.00/3.59  
% 10.00/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.00/3.59  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.00/3.59  
% 10.00/3.59  %Foreground sorts:
% 10.00/3.59  
% 10.00/3.59  
% 10.00/3.59  %Background operators:
% 10.00/3.59  
% 10.00/3.59  
% 10.00/3.59  %Foreground operators:
% 10.00/3.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.00/3.59  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 10.00/3.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.00/3.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.00/3.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.00/3.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.00/3.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.00/3.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.00/3.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.00/3.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.00/3.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.00/3.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.00/3.59  tff('#skF_5', type, '#skF_5': $i).
% 10.00/3.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.00/3.59  tff('#skF_2', type, '#skF_2': $i).
% 10.00/3.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.00/3.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.00/3.59  tff('#skF_3', type, '#skF_3': $i).
% 10.00/3.59  tff('#skF_1', type, '#skF_1': $i).
% 10.00/3.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.00/3.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.00/3.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.00/3.59  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.00/3.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.00/3.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.00/3.59  tff('#skF_4', type, '#skF_4': $i).
% 10.00/3.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.00/3.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.00/3.59  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.00/3.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.00/3.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.00/3.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.00/3.59  
% 10.00/3.62  tff(f_250, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 10.00/3.62  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.00/3.62  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.00/3.62  tff(f_165, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.00/3.62  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.00/3.62  tff(f_121, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 10.00/3.62  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.00/3.62  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 10.00/3.62  tff(f_32, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 10.00/3.62  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.00/3.62  tff(f_224, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 10.00/3.62  tff(f_153, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.00/3.62  tff(f_137, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.00/3.62  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.00/3.62  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 10.00/3.62  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 10.00/3.62  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.00/3.62  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.00/3.62  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 10.00/3.62  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 10.00/3.62  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 10.00/3.62  tff(f_101, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 10.00/3.62  tff(f_208, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 10.00/3.62  tff(f_163, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.00/3.62  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.00/3.62  tff(c_82, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_100, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_220, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.00/3.62  tff(c_241, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_220])).
% 10.00/3.62  tff(c_104, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_34, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.00/3.62  tff(c_88, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_66, plain, (![A_52]: (k6_relat_1(A_52)=k6_partfun1(A_52))), inference(cnfTransformation, [status(thm)], [f_165])).
% 10.00/3.62  tff(c_26, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.00/3.62  tff(c_110, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_26])).
% 10.00/3.62  tff(c_46, plain, (![A_28]: (k5_relat_1(A_28, k2_funct_1(A_28))=k6_relat_1(k1_relat_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.00/3.62  tff(c_1029, plain, (![A_143]: (k5_relat_1(A_143, k2_funct_1(A_143))=k6_partfun1(k1_relat_1(A_143)) | ~v2_funct_1(A_143) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46])).
% 10.00/3.62  tff(c_92, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_454, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.00/3.62  tff(c_467, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_454])).
% 10.00/3.62  tff(c_477, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_467])).
% 10.00/3.62  tff(c_510, plain, (![B_120, A_121]: (k9_relat_1(B_120, k2_relat_1(A_121))=k2_relat_1(k5_relat_1(A_121, B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.00/3.62  tff(c_519, plain, (![B_120]: (k2_relat_1(k5_relat_1('#skF_4', B_120))=k9_relat_1(B_120, '#skF_3') | ~v1_relat_1(B_120) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_510])).
% 10.00/3.62  tff(c_529, plain, (![B_120]: (k2_relat_1(k5_relat_1('#skF_4', B_120))=k9_relat_1(B_120, '#skF_3') | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_519])).
% 10.00/3.62  tff(c_1048, plain, (k2_relat_1(k6_partfun1(k1_relat_1('#skF_4')))=k9_relat_1(k2_funct_1('#skF_4'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1029, c_529])).
% 10.00/3.62  tff(c_1060, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_104, c_88, c_110, c_1048])).
% 10.00/3.62  tff(c_1062, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1060])).
% 10.00/3.62  tff(c_1139, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_1062])).
% 10.00/3.62  tff(c_1143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_241, c_104, c_1139])).
% 10.00/3.62  tff(c_1145, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1060])).
% 10.00/3.62  tff(c_94, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_240, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_94, c_220])).
% 10.00/3.62  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.00/3.62  tff(c_123, plain, (![A_70]: (k1_xboole_0=A_70 | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.00/3.62  tff(c_131, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_123])).
% 10.00/3.62  tff(c_86, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_140, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_86])).
% 10.00/3.62  tff(c_98, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_96, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_475, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_94, c_454])).
% 10.00/3.62  tff(c_78, plain, (![B_65, C_66, A_64]: (k6_partfun1(B_65)=k5_relat_1(k2_funct_1(C_66), C_66) | k1_xboole_0=B_65 | ~v2_funct_1(C_66) | k2_relset_1(A_64, B_65, C_66)!=B_65 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2(C_66, A_64, B_65) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_224])).
% 10.00/3.62  tff(c_9156, plain, (![B_419, C_420, A_421]: (k6_partfun1(B_419)=k5_relat_1(k2_funct_1(C_420), C_420) | B_419='#skF_1' | ~v2_funct_1(C_420) | k2_relset_1(A_421, B_419, C_420)!=B_419 | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(A_421, B_419))) | ~v1_funct_2(C_420, A_421, B_419) | ~v1_funct_1(C_420))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78])).
% 10.00/3.62  tff(c_9163, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_94, c_9156])).
% 10.00/3.62  tff(c_9175, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_475, c_9163])).
% 10.00/3.62  tff(c_9176, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_140, c_9175])).
% 10.00/3.62  tff(c_9209, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(splitLeft, [status(thm)], [c_9176])).
% 10.00/3.62  tff(c_102, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_62, plain, (![A_45]: (m1_subset_1(k6_partfun1(A_45), k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.00/3.62  tff(c_313, plain, (![A_101, B_102, D_103]: (r2_relset_1(A_101, B_102, D_103, D_103) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.00/3.62  tff(c_326, plain, (![A_45]: (r2_relset_1(A_45, A_45, k6_partfun1(A_45), k6_partfun1(A_45)))), inference(resolution, [status(thm)], [c_62, c_313])).
% 10.00/3.62  tff(c_8284, plain, (![B_386, A_385, D_388, E_390, C_387, F_389]: (m1_subset_1(k1_partfun1(A_385, B_386, C_387, D_388, E_390, F_389), k1_zfmisc_1(k2_zfmisc_1(A_385, D_388))) | ~m1_subset_1(F_389, k1_zfmisc_1(k2_zfmisc_1(C_387, D_388))) | ~v1_funct_1(F_389) | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))) | ~v1_funct_1(E_390))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.00/3.62  tff(c_90, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_7494, plain, (![D_351, C_352, A_353, B_354]: (D_351=C_352 | ~r2_relset_1(A_353, B_354, C_352, D_351) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.00/3.62  tff(c_7504, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_90, c_7494])).
% 10.00/3.62  tff(c_7523, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7504])).
% 10.00/3.62  tff(c_7585, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_7523])).
% 10.00/3.62  tff(c_8301, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_8284, c_7585])).
% 10.00/3.62  tff(c_8322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_100, c_98, c_94, c_8301])).
% 10.00/3.62  tff(c_8323, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_7523])).
% 10.00/3.62  tff(c_9903, plain, (![A_445, B_446, C_447, D_448]: (k2_relset_1(A_445, B_446, C_447)=B_446 | ~r2_relset_1(B_446, B_446, k1_partfun1(B_446, A_445, A_445, B_446, D_448, C_447), k6_partfun1(B_446)) | ~m1_subset_1(D_448, k1_zfmisc_1(k2_zfmisc_1(B_446, A_445))) | ~v1_funct_2(D_448, B_446, A_445) | ~v1_funct_1(D_448) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))) | ~v1_funct_2(C_447, A_445, B_446) | ~v1_funct_1(C_447))), inference(cnfTransformation, [status(thm)], [f_182])).
% 10.00/3.62  tff(c_9909, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8323, c_9903])).
% 10.00/3.62  tff(c_9913, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_104, c_102, c_100, c_326, c_475, c_9909])).
% 10.00/3.62  tff(c_9915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9209, c_9913])).
% 10.00/3.62  tff(c_9917, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_9176])).
% 10.00/3.62  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.00/3.62  tff(c_12, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.00/3.62  tff(c_112, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 10.00/3.62  tff(c_194, plain, (![A_81, B_82]: (r1_tarski(A_81, B_82) | ~m1_subset_1(A_81, k1_zfmisc_1(B_82)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.00/3.62  tff(c_210, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_112, c_194])).
% 10.00/3.62  tff(c_30, plain, (![B_22, A_21]: (k5_relat_1(B_22, k6_relat_1(A_21))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.00/3.62  tff(c_351, plain, (![B_110, A_111]: (k5_relat_1(B_110, k6_partfun1(A_111))=B_110 | ~r1_tarski(k2_relat_1(B_110), A_111) | ~v1_relat_1(B_110))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_30])).
% 10.00/3.62  tff(c_359, plain, (![B_110]: (k5_relat_1(B_110, k6_partfun1(k2_relat_1(B_110)))=B_110 | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_210, c_351])).
% 10.00/3.62  tff(c_9928, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9917, c_359])).
% 10.00/3.62  tff(c_9942, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_9928])).
% 10.00/3.62  tff(c_84, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.00/3.62  tff(c_139, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_84])).
% 10.00/3.62  tff(c_238, plain, (![A_45]: (v1_relat_1(k6_partfun1(A_45)))), inference(resolution, [status(thm)], [c_62, c_220])).
% 10.00/3.62  tff(c_24, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.00/3.62  tff(c_111, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_24])).
% 10.00/3.62  tff(c_28, plain, (![A_20]: (k5_relat_1(k6_relat_1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.00/3.62  tff(c_290, plain, (![A_99]: (k5_relat_1(k6_partfun1(k1_relat_1(A_99)), A_99)=A_99 | ~v1_relat_1(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_28])).
% 10.00/3.62  tff(c_299, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_290])).
% 10.00/3.62  tff(c_303, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_299])).
% 10.00/3.62  tff(c_105, plain, (![A_28]: (k5_relat_1(A_28, k2_funct_1(A_28))=k6_partfun1(k1_relat_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46])).
% 10.00/3.62  tff(c_482, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_477, c_359])).
% 10.00/3.62  tff(c_492, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_482])).
% 10.00/3.62  tff(c_109, plain, (![A_20]: (k5_relat_1(k6_partfun1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_28])).
% 10.00/3.62  tff(c_1213, plain, (![A_148, B_149, C_150]: (k5_relat_1(k5_relat_1(A_148, B_149), C_150)=k5_relat_1(A_148, k5_relat_1(B_149, C_150)) | ~v1_relat_1(C_150) | ~v1_relat_1(B_149) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.00/3.62  tff(c_1279, plain, (![A_20, C_150]: (k5_relat_1(k6_partfun1(k1_relat_1(A_20)), k5_relat_1(A_20, C_150))=k5_relat_1(A_20, C_150) | ~v1_relat_1(C_150) | ~v1_relat_1(A_20) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_20))) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_109, c_1213])).
% 10.00/3.62  tff(c_8575, plain, (![A_400, C_401]: (k5_relat_1(k6_partfun1(k1_relat_1(A_400)), k5_relat_1(A_400, C_401))=k5_relat_1(A_400, C_401) | ~v1_relat_1(C_401) | ~v1_relat_1(A_400))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_1279])).
% 10.00/3.62  tff(c_8629, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_492, c_8575])).
% 10.00/3.62  tff(c_8673, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_238, c_492, c_8629])).
% 10.00/3.62  tff(c_22, plain, (![A_12, B_16, C_18]: (k5_relat_1(k5_relat_1(A_12, B_16), C_18)=k5_relat_1(A_12, k5_relat_1(B_16, C_18)) | ~v1_relat_1(C_18) | ~v1_relat_1(B_16) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.00/3.62  tff(c_8693, plain, (![C_18]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k5_relat_1('#skF_4', C_18))=k5_relat_1('#skF_4', C_18) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_8673, c_22])).
% 10.00/3.62  tff(c_8854, plain, (![C_413]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k5_relat_1('#skF_4', C_413))=k5_relat_1('#skF_4', C_413) | ~v1_relat_1(C_413))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_241, c_8693])).
% 10.00/3.62  tff(c_8895, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1(k1_relat_1('#skF_4')))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_105, c_8854])).
% 10.00/3.62  tff(c_8924, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_104, c_88, c_1145, c_303, c_8895])).
% 10.00/3.62  tff(c_80, plain, (![A_64, C_66, B_65]: (k6_partfun1(A_64)=k5_relat_1(C_66, k2_funct_1(C_66)) | k1_xboole_0=B_65 | ~v2_funct_1(C_66) | k2_relset_1(A_64, B_65, C_66)!=B_65 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2(C_66, A_64, B_65) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_224])).
% 10.00/3.62  tff(c_10116, plain, (![A_452, C_453, B_454]: (k6_partfun1(A_452)=k5_relat_1(C_453, k2_funct_1(C_453)) | B_454='#skF_1' | ~v2_funct_1(C_453) | k2_relset_1(A_452, B_454, C_453)!=B_454 | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(A_452, B_454))) | ~v1_funct_2(C_453, A_452, B_454) | ~v1_funct_1(C_453))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_80])).
% 10.00/3.62  tff(c_10125, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_10116])).
% 10.00/3.62  tff(c_10139, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_92, c_88, c_8924, c_10125])).
% 10.00/3.62  tff(c_10140, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_139, c_10139])).
% 10.00/3.62  tff(c_10144, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10140, c_8924])).
% 10.00/3.62  tff(c_9918, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9917, c_475])).
% 10.00/3.62  tff(c_10123, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_94, c_10116])).
% 10.00/3.62  tff(c_10135, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_9918, c_10123])).
% 10.00/3.62  tff(c_10136, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_140, c_10135])).
% 10.00/3.62  tff(c_10285, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_10136])).
% 10.00/3.62  tff(c_38, plain, (![A_26]: (v2_funct_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.00/3.62  tff(c_107, plain, (![A_26]: (v2_funct_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_38])).
% 10.00/3.62  tff(c_72, plain, (![B_59, A_58, D_61, E_63, C_60]: (k1_xboole_0=C_60 | v2_funct_1(E_63) | k2_relset_1(A_58, B_59, D_61)!=B_59 | ~v2_funct_1(k1_partfun1(A_58, B_59, B_59, C_60, D_61, E_63)) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(B_59, C_60))) | ~v1_funct_2(E_63, B_59, C_60) | ~v1_funct_1(E_63) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(D_61, A_58, B_59) | ~v1_funct_1(D_61))), inference(cnfTransformation, [status(thm)], [f_208])).
% 10.00/3.62  tff(c_10800, plain, (![C_482, B_478, D_479, A_480, E_481]: (C_482='#skF_1' | v2_funct_1(E_481) | k2_relset_1(A_480, B_478, D_479)!=B_478 | ~v2_funct_1(k1_partfun1(A_480, B_478, B_478, C_482, D_479, E_481)) | ~m1_subset_1(E_481, k1_zfmisc_1(k2_zfmisc_1(B_478, C_482))) | ~v1_funct_2(E_481, B_478, C_482) | ~v1_funct_1(E_481) | ~m1_subset_1(D_479, k1_zfmisc_1(k2_zfmisc_1(A_480, B_478))) | ~v1_funct_2(D_479, A_480, B_478) | ~v1_funct_1(D_479))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_72])).
% 10.00/3.62  tff(c_10804, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8323, c_10800])).
% 10.00/3.62  tff(c_10809, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_98, c_96, c_94, c_107, c_92, c_10804])).
% 10.00/3.62  tff(c_10811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10285, c_140, c_10809])).
% 10.00/3.62  tff(c_10813, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_10136])).
% 10.00/3.62  tff(c_10812, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_10136])).
% 10.00/3.62  tff(c_18, plain, (![B_10, A_8]: (k9_relat_1(B_10, k2_relat_1(A_8))=k2_relat_1(k5_relat_1(A_8, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.00/3.62  tff(c_9925, plain, (![B_10]: (k2_relat_1(k5_relat_1('#skF_5', B_10))=k9_relat_1(B_10, '#skF_2') | ~v1_relat_1(B_10) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9917, c_18])).
% 10.00/3.62  tff(c_11617, plain, (![B_515]: (k2_relat_1(k5_relat_1('#skF_5', B_515))=k9_relat_1(B_515, '#skF_2') | ~v1_relat_1(B_515))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_9925])).
% 10.00/3.62  tff(c_11652, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_2')=k2_relat_1(k6_partfun1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10812, c_11617])).
% 10.00/3.62  tff(c_11680, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_2')='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_11652])).
% 10.00/3.62  tff(c_11691, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_11680])).
% 10.00/3.62  tff(c_11756, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_11691])).
% 10.00/3.62  tff(c_11760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_98, c_11756])).
% 10.00/3.62  tff(c_11762, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_11680])).
% 10.00/3.62  tff(c_8764, plain, (![C_410, E_409, F_407, D_408, A_411, B_406]: (k1_partfun1(A_411, B_406, C_410, D_408, E_409, F_407)=k5_relat_1(E_409, F_407) | ~m1_subset_1(F_407, k1_zfmisc_1(k2_zfmisc_1(C_410, D_408))) | ~v1_funct_1(F_407) | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(A_411, B_406))) | ~v1_funct_1(E_409))), inference(cnfTransformation, [status(thm)], [f_163])).
% 10.00/3.62  tff(c_8771, plain, (![A_411, B_406, E_409]: (k1_partfun1(A_411, B_406, '#skF_3', '#skF_2', E_409, '#skF_5')=k5_relat_1(E_409, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(A_411, B_406))) | ~v1_funct_1(E_409))), inference(resolution, [status(thm)], [c_94, c_8764])).
% 10.00/3.62  tff(c_9971, plain, (![A_449, B_450, E_451]: (k1_partfun1(A_449, B_450, '#skF_3', '#skF_2', E_451, '#skF_5')=k5_relat_1(E_451, '#skF_5') | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~v1_funct_1(E_451))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8771])).
% 10.00/3.62  tff(c_9984, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_9971])).
% 10.00/3.62  tff(c_9996, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_8323, c_9984])).
% 10.00/3.62  tff(c_10010, plain, (![C_18]: (k5_relat_1(k6_partfun1('#skF_2'), C_18)=k5_relat_1('#skF_4', k5_relat_1('#skF_5', C_18)) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9996, c_22])).
% 10.00/3.62  tff(c_13114, plain, (![C_535]: (k5_relat_1(k6_partfun1('#skF_2'), C_535)=k5_relat_1('#skF_4', k5_relat_1('#skF_5', C_535)) | ~v1_relat_1(C_535))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_240, c_10010])).
% 10.00/3.62  tff(c_442, plain, (![A_116]: (k1_relat_1(k2_funct_1(A_116))=k2_relat_1(A_116) | ~v2_funct_1(A_116) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.00/3.62  tff(c_11841, plain, (![A_517]: (k5_relat_1(k6_partfun1(k2_relat_1(A_517)), k2_funct_1(A_517))=k2_funct_1(A_517) | ~v1_relat_1(k2_funct_1(A_517)) | ~v2_funct_1(A_517) | ~v1_funct_1(A_517) | ~v1_relat_1(A_517))), inference(superposition, [status(thm), theory('equality')], [c_442, c_109])).
% 10.00/3.62  tff(c_11865, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9917, c_11841])).
% 10.00/3.62  tff(c_11898, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_98, c_10813, c_11762, c_11865])).
% 10.00/3.62  tff(c_13124, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_5', k2_funct_1('#skF_5')))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_13114, c_11898])).
% 10.00/3.62  tff(c_13201, plain, (k2_funct_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11762, c_492, c_10812, c_13124])).
% 10.00/3.62  tff(c_10971, plain, (k6_partfun1(k1_relat_1('#skF_5'))=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10812, c_105])).
% 10.00/3.62  tff(c_10982, plain, (k6_partfun1(k1_relat_1('#skF_5'))=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_98, c_10813, c_10971])).
% 10.00/3.62  tff(c_11061, plain, (k1_relat_1(k6_partfun1('#skF_3'))=k1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10982, c_111])).
% 10.00/3.62  tff(c_11093, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_11061])).
% 10.00/3.62  tff(c_14874, plain, (![A_584, C_585]: (k5_relat_1(k6_partfun1(k1_relat_1(A_584)), C_585)=k5_relat_1(A_584, k5_relat_1(k2_funct_1(A_584), C_585)) | ~v1_relat_1(C_585) | ~v1_relat_1(k2_funct_1(A_584)) | ~v1_relat_1(A_584) | ~v2_funct_1(A_584) | ~v1_funct_1(A_584) | ~v1_relat_1(A_584))), inference(superposition, [status(thm), theory('equality')], [c_105, c_1213])).
% 10.00/3.62  tff(c_15056, plain, (![C_585]: (k5_relat_1('#skF_5', k5_relat_1(k2_funct_1('#skF_5'), C_585))=k5_relat_1(k6_partfun1('#skF_3'), C_585) | ~v1_relat_1(C_585) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11093, c_14874])).
% 10.00/3.62  tff(c_15251, plain, (![C_586]: (k5_relat_1(k6_partfun1('#skF_3'), C_586)=k5_relat_1('#skF_5', k5_relat_1('#skF_4', C_586)) | ~v1_relat_1(C_586))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_98, c_10813, c_240, c_241, c_13201, c_13201, c_15056])).
% 10.00/3.62  tff(c_11883, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_477, c_11841])).
% 10.00/3.62  tff(c_11900, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_104, c_88, c_1145, c_11883])).
% 10.00/3.62  tff(c_15275, plain, (k5_relat_1('#skF_5', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_15251, c_11900])).
% 10.00/3.62  tff(c_15371, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1145, c_9942, c_10144, c_15275])).
% 10.00/3.62  tff(c_15373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_15371])).
% 10.00/3.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.00/3.62  
% 10.00/3.62  Inference rules
% 10.00/3.62  ----------------------
% 10.00/3.62  #Ref     : 0
% 10.00/3.62  #Sup     : 3326
% 10.00/3.62  #Fact    : 0
% 10.00/3.62  #Define  : 0
% 10.00/3.62  #Split   : 27
% 10.00/3.62  #Chain   : 0
% 10.00/3.62  #Close   : 0
% 10.00/3.62  
% 10.00/3.62  Ordering : KBO
% 10.00/3.62  
% 10.00/3.62  Simplification rules
% 10.00/3.62  ----------------------
% 10.00/3.62  #Subsume      : 185
% 10.00/3.62  #Demod        : 6286
% 10.00/3.62  #Tautology    : 1669
% 10.00/3.62  #SimpNegUnit  : 71
% 10.00/3.62  #BackRed      : 131
% 10.00/3.62  
% 10.00/3.62  #Partial instantiations: 0
% 10.00/3.62  #Strategies tried      : 1
% 10.00/3.62  
% 10.00/3.62  Timing (in seconds)
% 10.00/3.62  ----------------------
% 10.00/3.62  Preprocessing        : 0.38
% 10.00/3.62  Parsing              : 0.20
% 10.00/3.62  CNF conversion       : 0.03
% 10.00/3.62  Main loop            : 2.45
% 10.00/3.62  Inferencing          : 0.74
% 10.00/3.62  Reduction            : 1.06
% 10.00/3.62  Demodulation         : 0.85
% 10.00/3.62  BG Simplification    : 0.08
% 10.00/3.62  Subsumption          : 0.41
% 10.00/3.62  Abstraction          : 0.11
% 10.00/3.62  MUC search           : 0.00
% 10.00/3.62  Cooper               : 0.00
% 10.00/3.62  Total                : 2.90
% 10.00/3.62  Index Insertion      : 0.00
% 10.00/3.62  Index Deletion       : 0.00
% 10.00/3.62  Index Matching       : 0.00
% 10.00/3.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
