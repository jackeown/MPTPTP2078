%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:09 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 477 expanded)
%              Number of leaves         :   46 ( 186 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 (1461 expanded)
%              Number of equality atoms :   83 ( 200 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_170,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_128,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_59,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_129,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_177,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_195,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_177])).

tff(c_337,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_354,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_337])).

tff(c_403,plain,(
    ! [B_87,A_88] :
      ( k2_relat_1(B_87) = A_88
      | ~ v2_funct_2(B_87,A_88)
      | ~ v5_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_409,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_354,c_403])).

tff(c_424,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_409])).

tff(c_459,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_433,plain,(
    ! [A_89,B_90,D_91] :
      ( r2_relset_1(A_89,B_90,D_91,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_443,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_56,c_433])).

tff(c_470,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_487,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_470])).

tff(c_50,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_500,plain,(
    ! [D_97,C_98,A_99,B_100] :
      ( D_97 = C_98
      | ~ r2_relset_1(A_99,B_100,C_98,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_510,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_500])).

tff(c_529,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_510])).

tff(c_737,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_740,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_737])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_740])).

tff(c_745,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_1040,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k2_relset_1(A_164,B_165,C_166) = B_165
      | ~ r2_relset_1(B_165,B_165,k1_partfun1(B_165,A_164,A_164,B_165,D_167,C_166),k6_partfun1(B_165))
      | ~ m1_subset_1(D_167,k1_zfmisc_1(k2_zfmisc_1(B_165,A_164)))
      | ~ v1_funct_2(D_167,B_165,A_164)
      | ~ v1_funct_1(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_2(C_166,A_164,B_165)
      | ~ v1_funct_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1043,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_1040])).

tff(c_1045,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_443,c_487,c_1043])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_277,plain,(
    ! [B_71,A_72] :
      ( v5_relat_1(B_71,A_72)
      | ~ r1_tarski(k2_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_291,plain,(
    ! [B_71] :
      ( v5_relat_1(B_71,k2_relat_1(B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_367,plain,(
    ! [B_84] :
      ( v2_funct_2(B_84,k2_relat_1(B_84))
      | ~ v5_relat_1(B_84,k2_relat_1(B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_378,plain,(
    ! [B_71] :
      ( v2_funct_2(B_71,k2_relat_1(B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_291,c_367])).

tff(c_1058,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_378])).

tff(c_1077,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_1058])).

tff(c_1079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_1077])).

tff(c_1080,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_24,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_211,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_195,c_24])).

tff(c_228,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_1082,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_228])).

tff(c_58,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_1463,plain,(
    ! [A_207,D_205,C_209,F_208,B_206,E_210] :
      ( m1_subset_1(k1_partfun1(A_207,B_206,C_209,D_205,E_210,F_208),k1_zfmisc_1(k2_zfmisc_1(A_207,D_205)))
      | ~ m1_subset_1(F_208,k1_zfmisc_1(k2_zfmisc_1(C_209,D_205)))
      | ~ v1_funct_1(F_208)
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206)))
      | ~ v1_funct_1(E_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1215,plain,(
    ! [D_177,C_178,A_179,B_180] :
      ( D_177 = C_178
      | ~ r2_relset_1(A_179,B_180,C_178,D_177)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1225,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_1215])).

tff(c_1244,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1225])).

tff(c_1323,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1244])).

tff(c_1474,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1463,c_1323])).

tff(c_1495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1474])).

tff(c_1496,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1244])).

tff(c_1794,plain,(
    ! [E_252,D_255,A_251,B_253,C_254] :
      ( k1_xboole_0 = C_254
      | v2_funct_1(D_255)
      | ~ v2_funct_1(k1_partfun1(A_251,B_253,B_253,C_254,D_255,E_252))
      | ~ m1_subset_1(E_252,k1_zfmisc_1(k2_zfmisc_1(B_253,C_254)))
      | ~ v1_funct_2(E_252,B_253,C_254)
      | ~ v1_funct_1(E_252)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_251,B_253)))
      | ~ v1_funct_2(D_255,A_251,B_253)
      | ~ v1_funct_1(D_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1796,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_1794])).

tff(c_1798,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_81,c_1796])).

tff(c_1800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_1082,c_1798])).

tff(c_1801,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1816,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1801,c_1801,c_22])).

tff(c_26,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_210,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_195,c_26])).

tff(c_226,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_1804,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1801,c_226])).

tff(c_1887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1816,c_1804])).

tff(c_1888,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_194,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_177])).

tff(c_202,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_194,c_26])).

tff(c_212,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_1890,plain,(
    k1_relat_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_212])).

tff(c_2492,plain,(
    ! [E_330,C_329,F_328,D_325,A_327,B_326] :
      ( m1_subset_1(k1_partfun1(A_327,B_326,C_329,D_325,E_330,F_328),k1_zfmisc_1(k2_zfmisc_1(A_327,D_325)))
      | ~ m1_subset_1(F_328,k1_zfmisc_1(k2_zfmisc_1(C_329,D_325)))
      | ~ v1_funct_1(F_328)
      | ~ m1_subset_1(E_330,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326)))
      | ~ v1_funct_1(E_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2277,plain,(
    ! [D_300,C_301,A_302,B_303] :
      ( D_300 = C_301
      | ~ r2_relset_1(A_302,B_303,C_301,D_300)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303)))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2287,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_2277])).

tff(c_2306,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2287])).

tff(c_2319,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2306])).

tff(c_2503,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2492,c_2319])).

tff(c_2524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2503])).

tff(c_2525,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2306])).

tff(c_64,plain,(
    ! [E_44,D_42,A_39,C_41,B_40] :
      ( k1_xboole_0 = C_41
      | v2_funct_1(D_42)
      | ~ v2_funct_1(k1_partfun1(A_39,B_40,B_40,C_41,D_42,E_44))
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(B_40,C_41)))
      | ~ v1_funct_2(E_44,B_40,C_41)
      | ~ v1_funct_1(E_44)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_42,A_39,B_40)
      | ~ v1_funct_1(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2981,plain,(
    ! [A_397,E_398,B_399,C_400,D_401] :
      ( C_400 = '#skF_4'
      | v2_funct_1(D_401)
      | ~ v2_funct_1(k1_partfun1(A_397,B_399,B_399,C_400,D_401,E_398))
      | ~ m1_subset_1(E_398,k1_zfmisc_1(k2_zfmisc_1(B_399,C_400)))
      | ~ v1_funct_2(E_398,B_399,C_400)
      | ~ v1_funct_1(E_398)
      | ~ m1_subset_1(D_401,k1_zfmisc_1(k2_zfmisc_1(A_397,B_399)))
      | ~ v1_funct_2(D_401,A_397,B_399)
      | ~ v1_funct_1(D_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_64])).

tff(c_2983,plain,
    ( '#skF_1' = '#skF_4'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2525,c_2981])).

tff(c_2985,plain,
    ( '#skF_1' = '#skF_4'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_81,c_2983])).

tff(c_2986,plain,(
    '#skF_1' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_2985])).

tff(c_2024,plain,(
    ! [C_270,A_271,B_272] :
      ( v4_relat_1(C_270,A_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2040,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_2024])).

tff(c_3009,plain,(
    v4_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2986,c_2040])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_28])).

tff(c_30,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    ! [A_10] : v1_relat_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30])).

tff(c_118,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_82])).

tff(c_16,plain,(
    ! [A_7] : v4_relat_1(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_213,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k1_relat_1(B_63),A_64)
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_218,plain,(
    ! [A_64] :
      ( r1_tarski(k1_xboole_0,A_64)
      | ~ v4_relat_1(k1_xboole_0,A_64)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_213])).

tff(c_222,plain,(
    ! [A_65] : r1_tarski(k1_xboole_0,A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_16,c_218])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_225,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_222,c_2])).

tff(c_1990,plain,(
    ! [A_268] :
      ( A_268 = '#skF_4'
      | ~ r1_tarski(A_268,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1888,c_225])).

tff(c_2010,plain,(
    ! [B_4] :
      ( k1_relat_1(B_4) = '#skF_4'
      | ~ v4_relat_1(B_4,'#skF_4')
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_1990])).

tff(c_3022,plain,
    ( k1_relat_1('#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3009,c_2010])).

tff(c_3025,plain,(
    k1_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_3022])).

tff(c_3027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1890,c_3025])).

tff(c_3028,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_120,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_81])).

tff(c_3036,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3028,c_120])).

tff(c_3045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_3036])).

tff(c_3046,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3095,plain,(
    ! [C_409,A_410,B_411] :
      ( v1_relat_1(C_409)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3095])).

tff(c_3321,plain,(
    ! [A_436,B_437,D_438] :
      ( r2_relset_1(A_436,B_437,D_438,D_438)
      | ~ m1_subset_1(D_438,k1_zfmisc_1(k2_zfmisc_1(A_436,B_437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3331,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_56,c_3321])).

tff(c_3393,plain,(
    ! [A_444,B_445,C_446] :
      ( k2_relset_1(A_444,B_445,C_446) = k2_relat_1(C_446)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3410,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3393])).

tff(c_3619,plain,(
    ! [C_476,F_475,B_473,E_477,A_474,D_472] :
      ( m1_subset_1(k1_partfun1(A_474,B_473,C_476,D_472,E_477,F_475),k1_zfmisc_1(k2_zfmisc_1(A_474,D_472)))
      | ~ m1_subset_1(F_475,k1_zfmisc_1(k2_zfmisc_1(C_476,D_472)))
      | ~ v1_funct_1(F_475)
      | ~ m1_subset_1(E_477,k1_zfmisc_1(k2_zfmisc_1(A_474,B_473)))
      | ~ v1_funct_1(E_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3411,plain,(
    ! [D_447,C_448,A_449,B_450] :
      ( D_447 = C_448
      | ~ r2_relset_1(A_449,B_450,C_448,D_447)
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3421,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_3411])).

tff(c_3440,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3421])).

tff(c_3453,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3440])).

tff(c_3630,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3619,c_3453])).

tff(c_3651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_3630])).

tff(c_3652,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3440])).

tff(c_4143,plain,(
    ! [A_552,B_553,C_554,D_555] :
      ( k2_relset_1(A_552,B_553,C_554) = B_553
      | ~ r2_relset_1(B_553,B_553,k1_partfun1(B_553,A_552,A_552,B_553,D_555,C_554),k6_partfun1(B_553))
      | ~ m1_subset_1(D_555,k1_zfmisc_1(k2_zfmisc_1(B_553,A_552)))
      | ~ v1_funct_2(D_555,B_553,A_552)
      | ~ v1_funct_1(D_555)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_552,B_553)))
      | ~ v1_funct_2(C_554,A_552,B_553)
      | ~ v1_funct_1(C_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4146,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3652,c_4143])).

tff(c_4151,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_3331,c_3410,c_4146])).

tff(c_3224,plain,(
    ! [B_424,A_425] :
      ( v5_relat_1(B_424,A_425)
      | ~ r1_tarski(k2_relat_1(B_424),A_425)
      | ~ v1_relat_1(B_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3234,plain,(
    ! [B_424] :
      ( v5_relat_1(B_424,k2_relat_1(B_424))
      | ~ v1_relat_1(B_424) ) ),
    inference(resolution,[status(thm)],[c_6,c_3224])).

tff(c_3282,plain,(
    ! [B_433] :
      ( v2_funct_2(B_433,k2_relat_1(B_433))
      | ~ v5_relat_1(B_433,k2_relat_1(B_433))
      | ~ v1_relat_1(B_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3293,plain,(
    ! [B_424] :
      ( v2_funct_2(B_424,k2_relat_1(B_424))
      | ~ v1_relat_1(B_424) ) ),
    inference(resolution,[status(thm)],[c_3234,c_3282])).

tff(c_4165,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4151,c_3293])).

tff(c_4184,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3113,c_4165])).

tff(c_4186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3046,c_4184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.19  
% 5.64/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.19  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.64/2.19  
% 5.64/2.19  %Foreground sorts:
% 5.64/2.19  
% 5.64/2.19  
% 5.64/2.19  %Background operators:
% 5.64/2.19  
% 5.64/2.19  
% 5.64/2.19  %Foreground operators:
% 5.64/2.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.64/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.64/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.64/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.64/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.64/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.64/2.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.64/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.64/2.19  tff('#skF_2', type, '#skF_2': $i).
% 5.64/2.19  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.64/2.19  tff('#skF_3', type, '#skF_3': $i).
% 5.64/2.19  tff('#skF_1', type, '#skF_1': $i).
% 5.64/2.19  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.64/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.64/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.64/2.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.64/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.64/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.64/2.19  tff('#skF_4', type, '#skF_4': $i).
% 5.64/2.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.64/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.64/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.64/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.64/2.19  
% 5.64/2.22  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.64/2.22  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.64/2.22  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.64/2.22  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.64/2.22  tff(f_109, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.64/2.22  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.64/2.22  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.64/2.22  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.64/2.22  tff(f_128, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.64/2.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.64/2.22  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.64/2.22  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.64/2.22  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.64/2.22  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.64/2.22  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.64/2.22  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.64/2.22  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.64/2.22  tff(f_59, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.64/2.22  tff(f_47, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 5.64/2.22  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.64/2.22  tff(c_129, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 5.64/2.22  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.64/2.22  tff(c_177, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.64/2.22  tff(c_195, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_177])).
% 5.64/2.22  tff(c_337, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.64/2.22  tff(c_354, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_337])).
% 5.64/2.22  tff(c_403, plain, (![B_87, A_88]: (k2_relat_1(B_87)=A_88 | ~v2_funct_2(B_87, A_88) | ~v5_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.64/2.22  tff(c_409, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_354, c_403])).
% 5.64/2.22  tff(c_424, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_409])).
% 5.64/2.22  tff(c_459, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_424])).
% 5.64/2.22  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.64/2.22  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.64/2.22  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.64/2.22  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.64/2.22  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.64/2.22  tff(c_56, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.64/2.22  tff(c_433, plain, (![A_89, B_90, D_91]: (r2_relset_1(A_89, B_90, D_91, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.64/2.22  tff(c_443, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_56, c_433])).
% 5.64/2.22  tff(c_470, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.64/2.22  tff(c_487, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_470])).
% 5.64/2.22  tff(c_50, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.64/2.22  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.64/2.22  tff(c_500, plain, (![D_97, C_98, A_99, B_100]: (D_97=C_98 | ~r2_relset_1(A_99, B_100, C_98, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.64/2.22  tff(c_510, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_500])).
% 5.64/2.22  tff(c_529, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_510])).
% 5.64/2.22  tff(c_737, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_529])).
% 5.64/2.22  tff(c_740, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_737])).
% 5.64/2.22  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_740])).
% 5.64/2.22  tff(c_745, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_529])).
% 5.64/2.22  tff(c_1040, plain, (![A_164, B_165, C_166, D_167]: (k2_relset_1(A_164, B_165, C_166)=B_165 | ~r2_relset_1(B_165, B_165, k1_partfun1(B_165, A_164, A_164, B_165, D_167, C_166), k6_partfun1(B_165)) | ~m1_subset_1(D_167, k1_zfmisc_1(k2_zfmisc_1(B_165, A_164))) | ~v1_funct_2(D_167, B_165, A_164) | ~v1_funct_1(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_2(C_166, A_164, B_165) | ~v1_funct_1(C_166))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.64/2.22  tff(c_1043, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_745, c_1040])).
% 5.64/2.22  tff(c_1045, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_443, c_487, c_1043])).
% 5.64/2.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.64/2.22  tff(c_277, plain, (![B_71, A_72]: (v5_relat_1(B_71, A_72) | ~r1_tarski(k2_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.64/2.22  tff(c_291, plain, (![B_71]: (v5_relat_1(B_71, k2_relat_1(B_71)) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_6, c_277])).
% 5.64/2.22  tff(c_367, plain, (![B_84]: (v2_funct_2(B_84, k2_relat_1(B_84)) | ~v5_relat_1(B_84, k2_relat_1(B_84)) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.64/2.22  tff(c_378, plain, (![B_71]: (v2_funct_2(B_71, k2_relat_1(B_71)) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_291, c_367])).
% 5.64/2.22  tff(c_1058, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1045, c_378])).
% 5.64/2.22  tff(c_1077, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_1058])).
% 5.64/2.22  tff(c_1079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_459, c_1077])).
% 5.64/2.22  tff(c_1080, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_424])).
% 5.64/2.22  tff(c_24, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.64/2.22  tff(c_211, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_195, c_24])).
% 5.64/2.22  tff(c_228, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211])).
% 5.64/2.22  tff(c_1082, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_228])).
% 5.64/2.22  tff(c_58, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.64/2.22  tff(c_32, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.64/2.22  tff(c_81, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 5.64/2.22  tff(c_1463, plain, (![A_207, D_205, C_209, F_208, B_206, E_210]: (m1_subset_1(k1_partfun1(A_207, B_206, C_209, D_205, E_210, F_208), k1_zfmisc_1(k2_zfmisc_1(A_207, D_205))) | ~m1_subset_1(F_208, k1_zfmisc_1(k2_zfmisc_1(C_209, D_205))) | ~v1_funct_1(F_208) | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))) | ~v1_funct_1(E_210))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.64/2.22  tff(c_1215, plain, (![D_177, C_178, A_179, B_180]: (D_177=C_178 | ~r2_relset_1(A_179, B_180, C_178, D_177) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.64/2.22  tff(c_1225, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_1215])).
% 5.64/2.22  tff(c_1244, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1225])).
% 5.64/2.22  tff(c_1323, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1244])).
% 5.64/2.22  tff(c_1474, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1463, c_1323])).
% 5.64/2.22  tff(c_1495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1474])).
% 5.64/2.22  tff(c_1496, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1244])).
% 5.64/2.22  tff(c_1794, plain, (![E_252, D_255, A_251, B_253, C_254]: (k1_xboole_0=C_254 | v2_funct_1(D_255) | ~v2_funct_1(k1_partfun1(A_251, B_253, B_253, C_254, D_255, E_252)) | ~m1_subset_1(E_252, k1_zfmisc_1(k2_zfmisc_1(B_253, C_254))) | ~v1_funct_2(E_252, B_253, C_254) | ~v1_funct_1(E_252) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_251, B_253))) | ~v1_funct_2(D_255, A_251, B_253) | ~v1_funct_1(D_255))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.64/2.22  tff(c_1796, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1496, c_1794])).
% 5.64/2.22  tff(c_1798, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_81, c_1796])).
% 5.64/2.22  tff(c_1800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_1082, c_1798])).
% 5.64/2.22  tff(c_1801, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_211])).
% 5.64/2.22  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.64/2.22  tff(c_1816, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1801, c_1801, c_22])).
% 5.64/2.22  tff(c_26, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.64/2.22  tff(c_210, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_195, c_26])).
% 5.64/2.22  tff(c_226, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_210])).
% 5.64/2.22  tff(c_1804, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1801, c_226])).
% 5.64/2.22  tff(c_1887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1816, c_1804])).
% 5.64/2.22  tff(c_1888, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_210])).
% 5.64/2.22  tff(c_194, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_177])).
% 5.64/2.22  tff(c_202, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_194, c_26])).
% 5.64/2.22  tff(c_212, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_202])).
% 5.64/2.22  tff(c_1890, plain, (k1_relat_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_212])).
% 5.64/2.22  tff(c_2492, plain, (![E_330, C_329, F_328, D_325, A_327, B_326]: (m1_subset_1(k1_partfun1(A_327, B_326, C_329, D_325, E_330, F_328), k1_zfmisc_1(k2_zfmisc_1(A_327, D_325))) | ~m1_subset_1(F_328, k1_zfmisc_1(k2_zfmisc_1(C_329, D_325))) | ~v1_funct_1(F_328) | ~m1_subset_1(E_330, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))) | ~v1_funct_1(E_330))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.64/2.22  tff(c_2277, plain, (![D_300, C_301, A_302, B_303]: (D_300=C_301 | ~r2_relset_1(A_302, B_303, C_301, D_300) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.64/2.22  tff(c_2287, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_2277])).
% 5.64/2.22  tff(c_2306, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2287])).
% 5.64/2.22  tff(c_2319, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2306])).
% 5.64/2.22  tff(c_2503, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2492, c_2319])).
% 5.64/2.22  tff(c_2524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2503])).
% 5.64/2.22  tff(c_2525, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2306])).
% 5.64/2.22  tff(c_64, plain, (![E_44, D_42, A_39, C_41, B_40]: (k1_xboole_0=C_41 | v2_funct_1(D_42) | ~v2_funct_1(k1_partfun1(A_39, B_40, B_40, C_41, D_42, E_44)) | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(B_40, C_41))) | ~v1_funct_2(E_44, B_40, C_41) | ~v1_funct_1(E_44) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_42, A_39, B_40) | ~v1_funct_1(D_42))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.64/2.22  tff(c_2981, plain, (![A_397, E_398, B_399, C_400, D_401]: (C_400='#skF_4' | v2_funct_1(D_401) | ~v2_funct_1(k1_partfun1(A_397, B_399, B_399, C_400, D_401, E_398)) | ~m1_subset_1(E_398, k1_zfmisc_1(k2_zfmisc_1(B_399, C_400))) | ~v1_funct_2(E_398, B_399, C_400) | ~v1_funct_1(E_398) | ~m1_subset_1(D_401, k1_zfmisc_1(k2_zfmisc_1(A_397, B_399))) | ~v1_funct_2(D_401, A_397, B_399) | ~v1_funct_1(D_401))), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_64])).
% 5.64/2.22  tff(c_2983, plain, ('#skF_1'='#skF_4' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2525, c_2981])).
% 5.64/2.22  tff(c_2985, plain, ('#skF_1'='#skF_4' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_81, c_2983])).
% 5.64/2.22  tff(c_2986, plain, ('#skF_1'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_129, c_2985])).
% 5.64/2.22  tff(c_2024, plain, (![C_270, A_271, B_272]: (v4_relat_1(C_270, A_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.64/2.22  tff(c_2040, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_2024])).
% 5.64/2.22  tff(c_3009, plain, (v4_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2986, c_2040])).
% 5.64/2.22  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.64/2.22  tff(c_101, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.64/2.22  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.64/2.22  tff(c_107, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_101, c_28])).
% 5.64/2.22  tff(c_30, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.64/2.22  tff(c_82, plain, (![A_10]: (v1_relat_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30])).
% 5.64/2.22  tff(c_118, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_82])).
% 5.64/2.22  tff(c_16, plain, (![A_7]: (v4_relat_1(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.64/2.22  tff(c_213, plain, (![B_63, A_64]: (r1_tarski(k1_relat_1(B_63), A_64) | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.64/2.22  tff(c_218, plain, (![A_64]: (r1_tarski(k1_xboole_0, A_64) | ~v4_relat_1(k1_xboole_0, A_64) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_213])).
% 5.64/2.22  tff(c_222, plain, (![A_65]: (r1_tarski(k1_xboole_0, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_16, c_218])).
% 5.64/2.22  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.64/2.22  tff(c_225, plain, (![A_65]: (k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_xboole_0))), inference(resolution, [status(thm)], [c_222, c_2])).
% 5.64/2.22  tff(c_1990, plain, (![A_268]: (A_268='#skF_4' | ~r1_tarski(A_268, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1888, c_225])).
% 5.64/2.22  tff(c_2010, plain, (![B_4]: (k1_relat_1(B_4)='#skF_4' | ~v4_relat_1(B_4, '#skF_4') | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_1990])).
% 5.64/2.22  tff(c_3022, plain, (k1_relat_1('#skF_3')='#skF_4' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3009, c_2010])).
% 5.64/2.22  tff(c_3025, plain, (k1_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_194, c_3022])).
% 5.64/2.22  tff(c_3027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1890, c_3025])).
% 5.64/2.22  tff(c_3028, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_202])).
% 5.64/2.22  tff(c_120, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_81])).
% 5.64/2.22  tff(c_3036, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3028, c_120])).
% 5.64/2.22  tff(c_3045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_3036])).
% 5.64/2.22  tff(c_3046, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 5.64/2.22  tff(c_3095, plain, (![C_409, A_410, B_411]: (v1_relat_1(C_409) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.64/2.22  tff(c_3113, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3095])).
% 5.64/2.22  tff(c_3321, plain, (![A_436, B_437, D_438]: (r2_relset_1(A_436, B_437, D_438, D_438) | ~m1_subset_1(D_438, k1_zfmisc_1(k2_zfmisc_1(A_436, B_437))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.64/2.22  tff(c_3331, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_56, c_3321])).
% 5.64/2.22  tff(c_3393, plain, (![A_444, B_445, C_446]: (k2_relset_1(A_444, B_445, C_446)=k2_relat_1(C_446) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_444, B_445))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.64/2.22  tff(c_3410, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3393])).
% 5.64/2.22  tff(c_3619, plain, (![C_476, F_475, B_473, E_477, A_474, D_472]: (m1_subset_1(k1_partfun1(A_474, B_473, C_476, D_472, E_477, F_475), k1_zfmisc_1(k2_zfmisc_1(A_474, D_472))) | ~m1_subset_1(F_475, k1_zfmisc_1(k2_zfmisc_1(C_476, D_472))) | ~v1_funct_1(F_475) | ~m1_subset_1(E_477, k1_zfmisc_1(k2_zfmisc_1(A_474, B_473))) | ~v1_funct_1(E_477))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.64/2.22  tff(c_3411, plain, (![D_447, C_448, A_449, B_450]: (D_447=C_448 | ~r2_relset_1(A_449, B_450, C_448, D_447) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.64/2.22  tff(c_3421, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_3411])).
% 5.64/2.22  tff(c_3440, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3421])).
% 5.64/2.22  tff(c_3453, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3440])).
% 5.64/2.22  tff(c_3630, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3619, c_3453])).
% 5.64/2.22  tff(c_3651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_3630])).
% 5.64/2.22  tff(c_3652, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3440])).
% 5.64/2.22  tff(c_4143, plain, (![A_552, B_553, C_554, D_555]: (k2_relset_1(A_552, B_553, C_554)=B_553 | ~r2_relset_1(B_553, B_553, k1_partfun1(B_553, A_552, A_552, B_553, D_555, C_554), k6_partfun1(B_553)) | ~m1_subset_1(D_555, k1_zfmisc_1(k2_zfmisc_1(B_553, A_552))) | ~v1_funct_2(D_555, B_553, A_552) | ~v1_funct_1(D_555) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_552, B_553))) | ~v1_funct_2(C_554, A_552, B_553) | ~v1_funct_1(C_554))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.64/2.22  tff(c_4146, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3652, c_4143])).
% 5.64/2.22  tff(c_4151, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_3331, c_3410, c_4146])).
% 5.64/2.22  tff(c_3224, plain, (![B_424, A_425]: (v5_relat_1(B_424, A_425) | ~r1_tarski(k2_relat_1(B_424), A_425) | ~v1_relat_1(B_424))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.64/2.22  tff(c_3234, plain, (![B_424]: (v5_relat_1(B_424, k2_relat_1(B_424)) | ~v1_relat_1(B_424))), inference(resolution, [status(thm)], [c_6, c_3224])).
% 5.64/2.22  tff(c_3282, plain, (![B_433]: (v2_funct_2(B_433, k2_relat_1(B_433)) | ~v5_relat_1(B_433, k2_relat_1(B_433)) | ~v1_relat_1(B_433))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.64/2.22  tff(c_3293, plain, (![B_424]: (v2_funct_2(B_424, k2_relat_1(B_424)) | ~v1_relat_1(B_424))), inference(resolution, [status(thm)], [c_3234, c_3282])).
% 5.64/2.22  tff(c_4165, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4151, c_3293])).
% 5.64/2.22  tff(c_4184, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3113, c_4165])).
% 5.64/2.22  tff(c_4186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3046, c_4184])).
% 5.64/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.22  
% 5.64/2.22  Inference rules
% 5.64/2.22  ----------------------
% 5.64/2.22  #Ref     : 0
% 5.64/2.22  #Sup     : 816
% 5.64/2.22  #Fact    : 0
% 5.64/2.22  #Define  : 0
% 5.64/2.22  #Split   : 28
% 5.64/2.22  #Chain   : 0
% 5.64/2.22  #Close   : 0
% 5.64/2.22  
% 5.64/2.22  Ordering : KBO
% 5.64/2.22  
% 5.64/2.22  Simplification rules
% 5.64/2.22  ----------------------
% 5.64/2.22  #Subsume      : 113
% 5.64/2.22  #Demod        : 1094
% 5.64/2.22  #Tautology    : 316
% 5.64/2.22  #SimpNegUnit  : 9
% 5.64/2.22  #BackRed      : 113
% 5.64/2.22  
% 5.64/2.22  #Partial instantiations: 0
% 5.64/2.22  #Strategies tried      : 1
% 5.64/2.22  
% 5.64/2.22  Timing (in seconds)
% 5.64/2.22  ----------------------
% 5.64/2.22  Preprocessing        : 0.40
% 5.64/2.22  Parsing              : 0.22
% 5.64/2.22  CNF conversion       : 0.03
% 5.64/2.22  Main loop            : 0.92
% 5.64/2.22  Inferencing          : 0.33
% 5.64/2.22  Reduction            : 0.32
% 5.64/2.22  Demodulation         : 0.23
% 5.64/2.22  BG Simplification    : 0.03
% 5.64/2.22  Subsumption          : 0.16
% 5.64/2.22  Abstraction          : 0.04
% 5.64/2.22  MUC search           : 0.00
% 5.64/2.22  Cooper               : 0.00
% 5.64/2.22  Total                : 1.38
% 5.64/2.22  Index Insertion      : 0.00
% 5.64/2.22  Index Deletion       : 0.00
% 5.64/2.22  Index Matching       : 0.00
% 5.64/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
