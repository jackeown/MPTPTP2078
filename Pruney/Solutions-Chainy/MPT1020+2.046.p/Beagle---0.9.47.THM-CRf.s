%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:57 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 9.21s
% Verified   : 
% Statistics : Number of formulae       :  348 (4640 expanded)
%              Number of leaves         :   47 (1486 expanded)
%              Depth                    :   18
%              Number of atoms          :  658 (13528 expanded)
%              Number of equality atoms :  196 (3263 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_188,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_166,axiom,(
    ! [A,B,C] :
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

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_122,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_70,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_72,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_494,plain,(
    ! [A_102,B_103,D_104] :
      ( r2_relset_1(A_102,B_103,D_104,D_104)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_508,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_494])).

tff(c_86,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_84,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_80,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_28,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_241,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_247,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_241])).

tff(c_254,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_247])).

tff(c_258,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_276,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_258])).

tff(c_548,plain,(
    ! [B_109,A_110] :
      ( k2_relat_1(B_109) = A_110
      | ~ v2_funct_2(B_109,A_110)
      | ~ v5_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_563,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_276,c_548])).

tff(c_576,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_563])).

tff(c_947,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_82,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1086,plain,(
    ! [C_177,B_178,A_179] :
      ( v2_funct_2(C_177,B_178)
      | ~ v3_funct_2(C_177,A_179,B_178)
      | ~ v1_funct_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1093,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1086])).

tff(c_1106,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_1093])).

tff(c_1108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_947,c_1106])).

tff(c_1109,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_1121,plain,(
    ! [A_180,B_181,C_182] :
      ( k2_relset_1(A_180,B_181,C_182) = k2_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1128,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1121])).

tff(c_1140,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_1128])).

tff(c_1203,plain,(
    ! [C_187,A_188,B_189] :
      ( v2_funct_1(C_187)
      | ~ v3_funct_2(C_187,A_188,B_189)
      | ~ v1_funct_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1210,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1203])).

tff(c_1223,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_1210])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1836,plain,(
    ! [C_275,D_276,B_277,A_278] :
      ( k2_funct_1(C_275) = D_276
      | k1_xboole_0 = B_277
      | k1_xboole_0 = A_278
      | ~ v2_funct_1(C_275)
      | ~ r2_relset_1(A_278,A_278,k1_partfun1(A_278,B_277,B_277,A_278,C_275,D_276),k6_partfun1(A_278))
      | k2_relset_1(A_278,B_277,C_275) != B_277
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_zfmisc_1(B_277,A_278)))
      | ~ v1_funct_2(D_276,B_277,A_278)
      | ~ v1_funct_1(D_276)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_278,B_277)))
      | ~ v1_funct_2(C_275,A_278,B_277)
      | ~ v1_funct_1(C_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1839,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1836])).

tff(c_1845,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1140,c_1223,c_1839])).

tff(c_1848,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1845])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_394,plain,(
    ! [C_90,A_91,B_92] :
      ( v4_relat_1(C_90,A_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_420,plain,(
    ! [C_94,A_95] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_394])).

tff(c_425,plain,(
    ! [A_96,A_97] :
      ( v4_relat_1(A_96,A_97)
      | ~ r1_tarski(A_96,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_420])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [A_49,B_50] : v1_relat_1(k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_103])).

tff(c_124,plain,(
    ! [A_52] : k6_relat_1(A_52) = k6_partfun1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_130,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_34])).

tff(c_60,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_143,plain,(
    ! [A_53] : k1_relat_1(k6_partfun1(A_53)) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_30])).

tff(c_152,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_143])).

tff(c_323,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k1_relat_1(B_81),A_82)
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_335,plain,(
    ! [A_82] :
      ( r1_tarski(k1_xboole_0,A_82)
      | ~ v4_relat_1(k1_xboole_0,A_82)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_323])).

tff(c_343,plain,(
    ! [A_82] :
      ( r1_tarski(k1_xboole_0,A_82)
      | ~ v4_relat_1(k1_xboole_0,A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_335])).

tff(c_429,plain,(
    ! [A_97] :
      ( r1_tarski(k1_xboole_0,A_97)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_425,c_343])).

tff(c_432,plain,(
    ! [A_97] : r1_tarski(k1_xboole_0,A_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_429])).

tff(c_1870,plain,(
    ! [A_97] : r1_tarski('#skF_1',A_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_432])).

tff(c_1882,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_1848,c_14])).

tff(c_203,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_210,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_203])).

tff(c_228,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_236,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_210,c_228])).

tff(c_419,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_2059,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_419])).

tff(c_2067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1870,c_2059])).

tff(c_2068,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1845])).

tff(c_1433,plain,(
    ! [A_222,B_223] :
      ( k2_funct_2(A_222,B_223) = k2_funct_1(B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_zfmisc_1(A_222,A_222)))
      | ~ v3_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_1(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1440,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1433])).

tff(c_1455,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_1440])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1459,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1455,c_68])).

tff(c_2070,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2068,c_1459])).

tff(c_2074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_2070])).

tff(c_2075,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_2081,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2075,c_72])).

tff(c_3536,plain,(
    ! [A_452,B_453,D_454] :
      ( r2_relset_1(A_452,B_453,D_454,D_454)
      | ~ m1_subset_1(D_454,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3718,plain,(
    ! [D_475] :
      ( r2_relset_1('#skF_1','#skF_1',D_475,D_475)
      | ~ m1_subset_1(D_475,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_3536])).

tff(c_3726,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2081,c_3718])).

tff(c_2080,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2075,c_80])).

tff(c_2163,plain,(
    ! [B_287,A_288] :
      ( k2_relat_1(B_287) = A_288
      | ~ v2_funct_2(B_287,A_288)
      | ~ v5_relat_1(B_287,A_288)
      | ~ v1_relat_1(B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2181,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_276,c_2163])).

tff(c_2195,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_2181])).

tff(c_2837,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2195])).

tff(c_3137,plain,(
    ! [C_407,B_408,A_409] :
      ( v2_funct_2(C_407,B_408)
      | ~ v3_funct_2(C_407,A_409,B_408)
      | ~ v1_funct_1(C_407)
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_409,B_408))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3491,plain,(
    ! [C_449] :
      ( v2_funct_2(C_449,'#skF_1')
      | ~ v3_funct_2(C_449,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_449)
      | ~ m1_subset_1(C_449,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_3137])).

tff(c_3497,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2080,c_3491])).

tff(c_3507,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_3497])).

tff(c_3509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2837,c_3507])).

tff(c_3510,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2195])).

tff(c_3637,plain,(
    ! [A_466,B_467,C_468] :
      ( k2_relset_1(A_466,B_467,C_468) = k2_relat_1(C_468)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_466,B_467))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3777,plain,(
    ! [C_489] :
      ( k2_relset_1('#skF_1','#skF_1',C_489) = k2_relat_1(C_489)
      | ~ m1_subset_1(C_489,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_3637])).

tff(c_3783,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2080,c_3777])).

tff(c_3791,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3510,c_3783])).

tff(c_3755,plain,(
    ! [C_480,A_481,B_482] :
      ( v2_funct_1(C_480)
      | ~ v3_funct_2(C_480,A_481,B_482)
      | ~ v1_funct_1(C_480)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(A_481,B_482))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3914,plain,(
    ! [C_502] :
      ( v2_funct_1(C_502)
      | ~ v3_funct_2(C_502,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_502)
      | ~ m1_subset_1(C_502,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_3755])).

tff(c_3920,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2080,c_3914])).

tff(c_3930,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_3920])).

tff(c_5040,plain,(
    ! [C_625,D_626,B_627,A_628] :
      ( k2_funct_1(C_625) = D_626
      | k1_xboole_0 = B_627
      | k1_xboole_0 = A_628
      | ~ v2_funct_1(C_625)
      | ~ r2_relset_1(A_628,A_628,k1_partfun1(A_628,B_627,B_627,A_628,C_625,D_626),k6_partfun1(A_628))
      | k2_relset_1(A_628,B_627,C_625) != B_627
      | ~ m1_subset_1(D_626,k1_zfmisc_1(k2_zfmisc_1(B_627,A_628)))
      | ~ v1_funct_2(D_626,B_627,A_628)
      | ~ v1_funct_1(D_626)
      | ~ m1_subset_1(C_625,k1_zfmisc_1(k2_zfmisc_1(A_628,B_627)))
      | ~ v1_funct_2(C_625,A_628,B_627)
      | ~ v1_funct_1(C_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_5043,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_5040])).

tff(c_5049,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_2080,c_2075,c_78,c_76,c_2081,c_2075,c_3791,c_3930,c_5043])).

tff(c_5052,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5049])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2098,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_12])).

tff(c_2162,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2098])).

tff(c_5076,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5052,c_2162])).

tff(c_5087,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5052,c_5052,c_14])).

tff(c_5332,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5087,c_2075])).

tff(c_5334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5076,c_5332])).

tff(c_5335,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5049])).

tff(c_4118,plain,(
    ! [A_523,B_524] :
      ( k2_funct_2(A_523,B_524) = k2_funct_1(B_524)
      | ~ m1_subset_1(B_524,k1_zfmisc_1(k2_zfmisc_1(A_523,A_523)))
      | ~ v3_funct_2(B_524,A_523,A_523)
      | ~ v1_funct_2(B_524,A_523,A_523)
      | ~ v1_funct_1(B_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4977,plain,(
    ! [B_619] :
      ( k2_funct_2('#skF_1',B_619) = k2_funct_1(B_619)
      | ~ m1_subset_1(B_619,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_619,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_619,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_619) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_4118])).

tff(c_4983,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2080,c_4977])).

tff(c_4993,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_4983])).

tff(c_4999,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4993,c_68])).

tff(c_5337,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5335,c_4999])).

tff(c_5341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_5337])).

tff(c_5343,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2098])).

tff(c_5342,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2098])).

tff(c_5543,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5343,c_5343,c_5342])).

tff(c_5544,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5543])).

tff(c_301,plain,(
    ! [A_78,B_79,A_80] :
      ( v5_relat_1(A_78,B_79)
      | ~ r1_tarski(A_78,k2_zfmisc_1(A_80,B_79)) ) ),
    inference(resolution,[status(thm)],[c_20,c_258])).

tff(c_344,plain,(
    ! [A_83,B_84] : v5_relat_1(k2_zfmisc_1(A_83,B_84),B_84) ),
    inference(resolution,[status(thm)],[c_8,c_301])).

tff(c_350,plain,(
    ! [B_6] : v5_relat_1(k1_xboole_0,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_344])).

tff(c_32,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_160,plain,(
    ! [A_54] : k2_relat_1(k6_partfun1(A_54)) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_169,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_160])).

tff(c_2115,plain,(
    ! [B_285] :
      ( v2_funct_2(B_285,k2_relat_1(B_285))
      | ~ v5_relat_1(B_285,k2_relat_1(B_285))
      | ~ v1_relat_1(B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2126,plain,
    ( v2_funct_2(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ v5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2115])).

tff(c_2135,plain,(
    v2_funct_2(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_350,c_169,c_2126])).

tff(c_5377,plain,(
    v2_funct_2('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5343,c_5343,c_2135])).

tff(c_5555,plain,(
    v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5544,c_5544,c_5377])).

tff(c_5387,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5343,c_5343,c_169])).

tff(c_5344,plain,(
    ! [B_637,A_638] :
      ( k2_relat_1(B_637) = A_638
      | ~ v2_funct_2(B_637,A_638)
      | ~ v5_relat_1(B_637,A_638)
      | ~ v1_relat_1(B_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5362,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_276,c_5344])).

tff(c_5376,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_5362])).

tff(c_5482,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5387,c_5376])).

tff(c_5483,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5482])).

tff(c_5547,plain,(
    ~ v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5544,c_5483])).

tff(c_5677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5555,c_5547])).

tff(c_5678,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5543])).

tff(c_5679,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5543])).

tff(c_5711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_5679])).

tff(c_5712,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5482])).

tff(c_5726,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5712,c_5712,c_2080])).

tff(c_5723,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5712,c_5343])).

tff(c_407,plain,(
    ! [C_90,A_5] :
      ( v4_relat_1(C_90,A_5)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_394])).

tff(c_6060,plain,(
    ! [C_688,A_689] :
      ( v4_relat_1(C_688,A_689)
      | ~ m1_subset_1(C_688,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5723,c_407])).

tff(c_6068,plain,(
    ! [A_689] : v4_relat_1('#skF_1',A_689) ),
    inference(resolution,[status(thm)],[c_5726,c_6060])).

tff(c_5380,plain,(
    ! [A_82] :
      ( r1_tarski('#skF_2',A_82)
      | ~ v4_relat_1('#skF_2',A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5343,c_5343,c_343])).

tff(c_5999,plain,(
    ! [A_82] :
      ( r1_tarski('#skF_1',A_82)
      | ~ v4_relat_1('#skF_1',A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5712,c_5712,c_5380])).

tff(c_6072,plain,(
    ! [A_82] : r1_tarski('#skF_1',A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6068,c_5999])).

tff(c_211,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_203])).

tff(c_235,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_228])).

tff(c_353,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_2077,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2075,c_353])).

tff(c_5727,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5712,c_2077])).

tff(c_6080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6072,c_5727])).

tff(c_6081,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_6086,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6081,c_72])).

tff(c_10827,plain,(
    ! [A_1192,B_1193,D_1194] :
      ( r2_relset_1(A_1192,B_1193,D_1194,D_1194)
      | ~ m1_subset_1(D_1194,k1_zfmisc_1(k2_zfmisc_1(A_1192,B_1193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10975,plain,(
    ! [D_1215] :
      ( r2_relset_1('#skF_1','#skF_1',D_1215,D_1215)
      | ~ m1_subset_1(D_1215,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_10827])).

tff(c_10981,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_6086,c_10975])).

tff(c_74,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_250,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_241])).

tff(c_257,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_250])).

tff(c_277,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_258])).

tff(c_10241,plain,(
    ! [B_1117,A_1118] :
      ( k2_relat_1(B_1117) = A_1118
      | ~ v2_funct_2(B_1117,A_1118)
      | ~ v5_relat_1(B_1117,A_1118)
      | ~ v1_relat_1(B_1117) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_10256,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_277,c_10241])).

tff(c_10267,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_10256])).

tff(c_10274,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_10267])).

tff(c_10636,plain,(
    ! [C_1172,B_1173,A_1174] :
      ( v2_funct_2(C_1172,B_1173)
      | ~ v3_funct_2(C_1172,A_1174,B_1173)
      | ~ v1_funct_1(C_1172)
      | ~ m1_subset_1(C_1172,k1_zfmisc_1(k2_zfmisc_1(A_1174,B_1173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10792,plain,(
    ! [C_1190] :
      ( v2_funct_2(C_1190,'#skF_1')
      | ~ v3_funct_2(C_1190,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1190)
      | ~ m1_subset_1(C_1190,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_10636])).

tff(c_10795,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6086,c_10792])).

tff(c_10802,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_10795])).

tff(c_10804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10274,c_10802])).

tff(c_10805,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10267])).

tff(c_10938,plain,(
    ! [A_1209,B_1210,C_1211] :
      ( k2_relset_1(A_1209,B_1210,C_1211) = k2_relat_1(C_1211)
      | ~ m1_subset_1(C_1211,k1_zfmisc_1(k2_zfmisc_1(A_1209,B_1210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_11074,plain,(
    ! [C_1232] :
      ( k2_relset_1('#skF_1','#skF_1',C_1232) = k2_relat_1(C_1232)
      | ~ m1_subset_1(C_1232,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_10938])).

tff(c_11077,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6086,c_11074])).

tff(c_11083,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10805,c_11077])).

tff(c_11012,plain,(
    ! [C_1222,A_1223,B_1224] :
      ( v2_funct_1(C_1222)
      | ~ v3_funct_2(C_1222,A_1223,B_1224)
      | ~ v1_funct_1(C_1222)
      | ~ m1_subset_1(C_1222,k1_zfmisc_1(k2_zfmisc_1(A_1223,B_1224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_11187,plain,(
    ! [C_1244] :
      ( v2_funct_1(C_1244)
      | ~ v3_funct_2(C_1244,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1244)
      | ~ m1_subset_1(C_1244,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_11012])).

tff(c_11190,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6086,c_11187])).

tff(c_11197,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_11190])).

tff(c_7439,plain,(
    ! [A_846,B_847,D_848] :
      ( r2_relset_1(A_846,B_847,D_848,D_848)
      | ~ m1_subset_1(D_848,k1_zfmisc_1(k2_zfmisc_1(A_846,B_847))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7461,plain,(
    ! [D_855] :
      ( r2_relset_1('#skF_1','#skF_1',D_855,D_855)
      | ~ m1_subset_1(D_855,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_7439])).

tff(c_7469,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_6086,c_7461])).

tff(c_6085,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6081,c_80])).

tff(c_6354,plain,(
    ! [B_718,A_719] :
      ( k2_relat_1(B_718) = A_719
      | ~ v2_funct_2(B_718,A_719)
      | ~ v5_relat_1(B_718,A_719)
      | ~ v1_relat_1(B_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6372,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_276,c_6354])).

tff(c_6386,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_6372])).

tff(c_7008,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6386])).

tff(c_7325,plain,(
    ! [C_836,B_837,A_838] :
      ( v2_funct_2(C_836,B_837)
      | ~ v3_funct_2(C_836,A_838,B_837)
      | ~ v1_funct_1(C_836)
      | ~ m1_subset_1(C_836,k1_zfmisc_1(k2_zfmisc_1(A_838,B_837))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7361,plain,(
    ! [C_843] :
      ( v2_funct_2(C_843,'#skF_1')
      | ~ v3_funct_2(C_843,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_843)
      | ~ m1_subset_1(C_843,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_7325])).

tff(c_7367,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6085,c_7361])).

tff(c_7377,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_7367])).

tff(c_7379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7008,c_7377])).

tff(c_7380,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6386])).

tff(c_7500,plain,(
    ! [A_860,B_861,C_862] :
      ( k2_relset_1(A_860,B_861,C_862) = k2_relat_1(C_862)
      | ~ m1_subset_1(C_862,k1_zfmisc_1(k2_zfmisc_1(A_860,B_861))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7577,plain,(
    ! [C_870] :
      ( k2_relset_1('#skF_1','#skF_1',C_870) = k2_relat_1(C_870)
      | ~ m1_subset_1(C_870,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_7500])).

tff(c_7583,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6085,c_7577])).

tff(c_7591,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7380,c_7583])).

tff(c_7650,plain,(
    ! [C_876,A_877,B_878] :
      ( v2_funct_1(C_876)
      | ~ v3_funct_2(C_876,A_877,B_878)
      | ~ v1_funct_1(C_876)
      | ~ m1_subset_1(C_876,k1_zfmisc_1(k2_zfmisc_1(A_877,B_878))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7689,plain,(
    ! [C_883] :
      ( v2_funct_1(C_883)
      | ~ v3_funct_2(C_883,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_883)
      | ~ m1_subset_1(C_883,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_7650])).

tff(c_7695,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6085,c_7689])).

tff(c_7705,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_7695])).

tff(c_9136,plain,(
    ! [C_1036,D_1037,B_1038,A_1039] :
      ( k2_funct_1(C_1036) = D_1037
      | k1_xboole_0 = B_1038
      | k1_xboole_0 = A_1039
      | ~ v2_funct_1(C_1036)
      | ~ r2_relset_1(A_1039,A_1039,k1_partfun1(A_1039,B_1038,B_1038,A_1039,C_1036,D_1037),k6_partfun1(A_1039))
      | k2_relset_1(A_1039,B_1038,C_1036) != B_1038
      | ~ m1_subset_1(D_1037,k1_zfmisc_1(k2_zfmisc_1(B_1038,A_1039)))
      | ~ v1_funct_2(D_1037,B_1038,A_1039)
      | ~ v1_funct_1(D_1037)
      | ~ m1_subset_1(C_1036,k1_zfmisc_1(k2_zfmisc_1(A_1039,B_1038)))
      | ~ v1_funct_2(C_1036,A_1039,B_1038)
      | ~ v1_funct_1(C_1036) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_9139,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_9136])).

tff(c_9145,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_6085,c_6081,c_78,c_76,c_6086,c_6081,c_7591,c_7705,c_9139])).

tff(c_9148,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9145])).

tff(c_6100,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_12])).

tff(c_6170,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6100])).

tff(c_9183,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9148,c_6170])).

tff(c_9193,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9148,c_9148,c_14])).

tff(c_9464,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9193,c_6081])).

tff(c_9466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9183,c_9464])).

tff(c_9467,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9145])).

tff(c_8746,plain,(
    ! [A_994,B_995] :
      ( k2_funct_2(A_994,B_995) = k2_funct_1(B_995)
      | ~ m1_subset_1(B_995,k1_zfmisc_1(k2_zfmisc_1(A_994,A_994)))
      | ~ v3_funct_2(B_995,A_994,A_994)
      | ~ v1_funct_2(B_995,A_994,A_994)
      | ~ v1_funct_1(B_995) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_9074,plain,(
    ! [B_1032] :
      ( k2_funct_2('#skF_1',B_1032) = k2_funct_1(B_1032)
      | ~ m1_subset_1(B_1032,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_1032,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_1032,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_1032) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_8746])).

tff(c_9080,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6085,c_9074])).

tff(c_9090,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_9080])).

tff(c_9096,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9090,c_68])).

tff(c_9470,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9467,c_9096])).

tff(c_9474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7469,c_9470])).

tff(c_9476,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6100])).

tff(c_9475,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6100])).

tff(c_9614,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9476,c_9476,c_9475])).

tff(c_9615,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9614])).

tff(c_9633,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9615,c_9615,c_6086])).

tff(c_9487,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9476,c_9476,c_14])).

tff(c_9765,plain,(
    ! [A_1067] : k2_zfmisc_1(A_1067,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9615,c_9615,c_9487])).

tff(c_40,plain,(
    ! [C_20,A_18,B_19] :
      ( v4_relat_1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10013,plain,(
    ! [C_1093,A_1094] :
      ( v4_relat_1(C_1093,A_1094)
      | ~ m1_subset_1(C_1093,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9765,c_40])).

tff(c_10022,plain,(
    ! [A_1094] : v4_relat_1('#skF_1',A_1094) ),
    inference(resolution,[status(thm)],[c_9633,c_10013])).

tff(c_9630,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9615,c_9476])).

tff(c_9907,plain,(
    ! [A_82] :
      ( r1_tarski('#skF_1',A_82)
      | ~ v4_relat_1('#skF_1',A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9630,c_9630,c_343])).

tff(c_10041,plain,(
    ! [A_82] : r1_tarski('#skF_1',A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10022,c_9907])).

tff(c_6084,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6081,c_210])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6116,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6084,c_4])).

tff(c_6158,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6116])).

tff(c_9632,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9615,c_6158])).

tff(c_10047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10041,c_9632])).

tff(c_10048,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9614])).

tff(c_10049,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9614])).

tff(c_10082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10048,c_10049])).

tff(c_10083,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6116])).

tff(c_10089,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10083,c_70])).

tff(c_12499,plain,(
    ! [C_1388,D_1389,B_1390,A_1391] :
      ( k2_funct_1(C_1388) = D_1389
      | k1_xboole_0 = B_1390
      | k1_xboole_0 = A_1391
      | ~ v2_funct_1(C_1388)
      | ~ r2_relset_1(A_1391,A_1391,k1_partfun1(A_1391,B_1390,B_1390,A_1391,C_1388,D_1389),k6_partfun1(A_1391))
      | k2_relset_1(A_1391,B_1390,C_1388) != B_1390
      | ~ m1_subset_1(D_1389,k1_zfmisc_1(k2_zfmisc_1(B_1390,A_1391)))
      | ~ v1_funct_2(D_1389,B_1390,A_1391)
      | ~ v1_funct_1(D_1389)
      | ~ m1_subset_1(C_1388,k1_zfmisc_1(k2_zfmisc_1(A_1391,B_1390)))
      | ~ v1_funct_2(C_1388,A_1391,B_1390)
      | ~ v1_funct_1(C_1388) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_12502,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10089,c_12499])).

tff(c_12508,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_6086,c_6081,c_11083,c_11197,c_12502])).

tff(c_12511,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12508])).

tff(c_10131,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6100])).

tff(c_12542,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12511,c_10131])).

tff(c_12554,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12511,c_12511,c_16])).

tff(c_12813,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12554,c_6081])).

tff(c_12815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12542,c_12813])).

tff(c_12816,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12508])).

tff(c_12055,plain,(
    ! [A_1337,B_1338] :
      ( k2_funct_2(A_1337,B_1338) = k2_funct_1(B_1338)
      | ~ m1_subset_1(B_1338,k1_zfmisc_1(k2_zfmisc_1(A_1337,A_1337)))
      | ~ v3_funct_2(B_1338,A_1337,A_1337)
      | ~ v1_funct_2(B_1338,A_1337,A_1337)
      | ~ v1_funct_1(B_1338) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12842,plain,(
    ! [B_1405] :
      ( k2_funct_2('#skF_1',B_1405) = k2_funct_1(B_1405)
      | ~ m1_subset_1(B_1405,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_1405,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_1405,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_1405) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6081,c_12055])).

tff(c_12845,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6086,c_12842])).

tff(c_12852,plain,(
    k2_funct_2('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_12816,c_12845])).

tff(c_10090,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10083,c_68])).

tff(c_12854,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12852,c_10090])).

tff(c_12857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10981,c_12854])).

tff(c_12859,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6100])).

tff(c_12858,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6100])).

tff(c_12991,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12859,c_12859,c_12858])).

tff(c_12992,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12991])).

tff(c_13007,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12992,c_12992,c_6086])).

tff(c_13005,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12992,c_12859])).

tff(c_10115,plain,(
    ! [C_1101,A_1102,B_1103] :
      ( v4_relat_1(C_1101,A_1102)
      | ~ m1_subset_1(C_1101,k1_zfmisc_1(k2_zfmisc_1(A_1102,B_1103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10125,plain,(
    ! [C_1101,A_5] :
      ( v4_relat_1(C_1101,A_5)
      | ~ m1_subset_1(C_1101,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_10115])).

tff(c_13302,plain,(
    ! [C_1438,A_1439] :
      ( v4_relat_1(C_1438,A_1439)
      | ~ m1_subset_1(C_1438,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13005,c_10125])).

tff(c_13308,plain,(
    ! [A_1439] : v4_relat_1('#skF_1',A_1439) ),
    inference(resolution,[status(thm)],[c_13007,c_13302])).

tff(c_13239,plain,(
    ! [A_82] :
      ( r1_tarski('#skF_1',A_82)
      | ~ v4_relat_1('#skF_1',A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13005,c_13005,c_343])).

tff(c_13312,plain,(
    ! [A_82] : r1_tarski('#skF_1',A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13308,c_13239])).

tff(c_12958,plain,(
    ! [A_1408,B_1409,D_1410] :
      ( r2_relset_1(A_1408,B_1409,D_1410,D_1410)
      | ~ m1_subset_1(D_1410,k1_zfmisc_1(k2_zfmisc_1(A_1408,B_1409))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13626,plain,(
    ! [A_1489,B_1490,A_1491] :
      ( r2_relset_1(A_1489,B_1490,A_1491,A_1491)
      | ~ r1_tarski(A_1491,k2_zfmisc_1(A_1489,B_1490)) ) ),
    inference(resolution,[status(thm)],[c_20,c_12958])).

tff(c_13640,plain,(
    ! [A_1489,B_1490] : r2_relset_1(A_1489,B_1490,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_13312,c_13626])).

tff(c_13011,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12992,c_76])).

tff(c_13010,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12992,c_74])).

tff(c_13012,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12992,c_78])).

tff(c_36,plain,(
    ! [A_17] : k2_funct_1(k6_relat_1(A_17)) = k6_relat_1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_176,plain,(
    ! [A_55] : k2_funct_1(k6_partfun1(A_55)) = k6_partfun1(A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_36])).

tff(c_185,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_176])).

tff(c_188,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_185])).

tff(c_12867,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12859,c_12859,c_188])).

tff(c_12996,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12992,c_12992,c_12867])).

tff(c_13315,plain,(
    ! [A_1441,B_1442] :
      ( k2_funct_2(A_1441,B_1442) = k2_funct_1(B_1442)
      | ~ m1_subset_1(B_1442,k1_zfmisc_1(k2_zfmisc_1(A_1441,A_1441)))
      | ~ v3_funct_2(B_1442,A_1441,A_1441)
      | ~ v1_funct_2(B_1442,A_1441,A_1441)
      | ~ v1_funct_1(B_1442) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_14281,plain,(
    ! [A_1573,A_1574] :
      ( k2_funct_2(A_1573,A_1574) = k2_funct_1(A_1574)
      | ~ v3_funct_2(A_1574,A_1573,A_1573)
      | ~ v1_funct_2(A_1574,A_1573,A_1573)
      | ~ v1_funct_1(A_1574)
      | ~ r1_tarski(A_1574,k2_zfmisc_1(A_1573,A_1573)) ) ),
    inference(resolution,[status(thm)],[c_20,c_13315])).

tff(c_14285,plain,(
    ! [A_1573] :
      ( k2_funct_2(A_1573,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1573,A_1573)
      | ~ v1_funct_2('#skF_1',A_1573,A_1573)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_13312,c_14281])).

tff(c_14376,plain,(
    ! [A_1584] :
      ( k2_funct_2(A_1584,'#skF_1') = '#skF_1'
      | ~ v3_funct_2('#skF_1',A_1584,A_1584)
      | ~ v1_funct_2('#skF_1',A_1584,A_1584) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13012,c_12996,c_14285])).

tff(c_14379,plain,
    ( k2_funct_2('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_13010,c_14376])).

tff(c_14382,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13011,c_14379])).

tff(c_12998,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12992,c_12992,c_10090])).

tff(c_14383,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14382,c_12998])).

tff(c_14386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13640,c_14383])).

tff(c_14387,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12991])).

tff(c_14388,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12991])).

tff(c_14420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14387,c_14388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/3.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.93/3.36  
% 8.93/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.93/3.36  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.93/3.36  
% 8.93/3.36  %Foreground sorts:
% 8.93/3.36  
% 8.93/3.36  
% 8.93/3.36  %Background operators:
% 8.93/3.36  
% 8.93/3.36  
% 8.93/3.36  %Foreground operators:
% 8.93/3.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.93/3.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.93/3.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.93/3.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.93/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.93/3.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.93/3.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.93/3.36  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.93/3.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.93/3.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.93/3.36  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.93/3.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.93/3.36  tff('#skF_2', type, '#skF_2': $i).
% 8.93/3.36  tff('#skF_3', type, '#skF_3': $i).
% 8.93/3.36  tff('#skF_1', type, '#skF_1': $i).
% 8.93/3.36  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.93/3.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.93/3.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.93/3.36  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.93/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.93/3.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.93/3.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.93/3.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.93/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.93/3.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.93/3.36  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.93/3.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.93/3.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.93/3.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.93/3.36  
% 9.21/3.40  tff(f_188, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 9.21/3.40  tff(f_90, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.21/3.40  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.21/3.40  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.21/3.40  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.21/3.40  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.21/3.40  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 9.21/3.40  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.21/3.40  tff(f_166, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 9.21/3.40  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.21/3.40  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.21/3.40  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.21/3.40  tff(f_122, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.21/3.40  tff(f_70, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 9.21/3.40  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.21/3.40  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.21/3.40  tff(f_120, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 9.21/3.40  tff(f_72, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 9.21/3.40  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_494, plain, (![A_102, B_103, D_104]: (r2_relset_1(A_102, B_103, D_104, D_104) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.21/3.40  tff(c_508, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_494])).
% 9.21/3.40  tff(c_86, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_84, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_80, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.21/3.40  tff(c_241, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.21/3.40  tff(c_247, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_241])).
% 9.21/3.40  tff(c_254, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_247])).
% 9.21/3.40  tff(c_258, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.40  tff(c_276, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_258])).
% 9.21/3.40  tff(c_548, plain, (![B_109, A_110]: (k2_relat_1(B_109)=A_110 | ~v2_funct_2(B_109, A_110) | ~v5_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.21/3.40  tff(c_563, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_276, c_548])).
% 9.21/3.40  tff(c_576, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_563])).
% 9.21/3.40  tff(c_947, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_576])).
% 9.21/3.40  tff(c_82, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_1086, plain, (![C_177, B_178, A_179]: (v2_funct_2(C_177, B_178) | ~v3_funct_2(C_177, A_179, B_178) | ~v1_funct_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.21/3.40  tff(c_1093, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1086])).
% 9.21/3.40  tff(c_1106, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_1093])).
% 9.21/3.40  tff(c_1108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_947, c_1106])).
% 9.21/3.40  tff(c_1109, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_576])).
% 9.21/3.40  tff(c_1121, plain, (![A_180, B_181, C_182]: (k2_relset_1(A_180, B_181, C_182)=k2_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.21/3.40  tff(c_1128, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1121])).
% 9.21/3.40  tff(c_1140, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_1128])).
% 9.21/3.40  tff(c_1203, plain, (![C_187, A_188, B_189]: (v2_funct_1(C_187) | ~v3_funct_2(C_187, A_188, B_189) | ~v1_funct_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.21/3.40  tff(c_1210, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1203])).
% 9.21/3.40  tff(c_1223, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_1210])).
% 9.21/3.40  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_1836, plain, (![C_275, D_276, B_277, A_278]: (k2_funct_1(C_275)=D_276 | k1_xboole_0=B_277 | k1_xboole_0=A_278 | ~v2_funct_1(C_275) | ~r2_relset_1(A_278, A_278, k1_partfun1(A_278, B_277, B_277, A_278, C_275, D_276), k6_partfun1(A_278)) | k2_relset_1(A_278, B_277, C_275)!=B_277 | ~m1_subset_1(D_276, k1_zfmisc_1(k2_zfmisc_1(B_277, A_278))) | ~v1_funct_2(D_276, B_277, A_278) | ~v1_funct_1(D_276) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_278, B_277))) | ~v1_funct_2(C_275, A_278, B_277) | ~v1_funct_1(C_275))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.21/3.40  tff(c_1839, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1836])).
% 9.21/3.40  tff(c_1845, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1140, c_1223, c_1839])).
% 9.21/3.40  tff(c_1848, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1845])).
% 9.21/3.40  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.21/3.40  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.21/3.40  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.21/3.40  tff(c_394, plain, (![C_90, A_91, B_92]: (v4_relat_1(C_90, A_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.40  tff(c_420, plain, (![C_94, A_95]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_394])).
% 9.21/3.40  tff(c_425, plain, (![A_96, A_97]: (v4_relat_1(A_96, A_97) | ~r1_tarski(A_96, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_420])).
% 9.21/3.40  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.21/3.40  tff(c_103, plain, (![A_49, B_50]: (v1_relat_1(k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.21/3.40  tff(c_105, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_103])).
% 9.21/3.40  tff(c_124, plain, (![A_52]: (k6_relat_1(A_52)=k6_partfun1(A_52))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.21/3.40  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.21/3.40  tff(c_130, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_124, c_34])).
% 9.21/3.40  tff(c_60, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.21/3.40  tff(c_30, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.21/3.40  tff(c_143, plain, (![A_53]: (k1_relat_1(k6_partfun1(A_53))=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30])).
% 9.21/3.40  tff(c_152, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_130, c_143])).
% 9.21/3.40  tff(c_323, plain, (![B_81, A_82]: (r1_tarski(k1_relat_1(B_81), A_82) | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.21/3.40  tff(c_335, plain, (![A_82]: (r1_tarski(k1_xboole_0, A_82) | ~v4_relat_1(k1_xboole_0, A_82) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_152, c_323])).
% 9.21/3.40  tff(c_343, plain, (![A_82]: (r1_tarski(k1_xboole_0, A_82) | ~v4_relat_1(k1_xboole_0, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_335])).
% 9.21/3.40  tff(c_429, plain, (![A_97]: (r1_tarski(k1_xboole_0, A_97) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_425, c_343])).
% 9.21/3.40  tff(c_432, plain, (![A_97]: (r1_tarski(k1_xboole_0, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_429])).
% 9.21/3.40  tff(c_1870, plain, (![A_97]: (r1_tarski('#skF_1', A_97))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_432])).
% 9.21/3.40  tff(c_1882, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_1848, c_14])).
% 9.21/3.40  tff(c_203, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.21/3.40  tff(c_210, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_203])).
% 9.21/3.40  tff(c_228, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.21/3.40  tff(c_236, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_210, c_228])).
% 9.21/3.40  tff(c_419, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_236])).
% 9.21/3.40  tff(c_2059, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_419])).
% 9.21/3.40  tff(c_2067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1870, c_2059])).
% 9.21/3.40  tff(c_2068, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1845])).
% 9.21/3.40  tff(c_1433, plain, (![A_222, B_223]: (k2_funct_2(A_222, B_223)=k2_funct_1(B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_zfmisc_1(A_222, A_222))) | ~v3_funct_2(B_223, A_222, A_222) | ~v1_funct_2(B_223, A_222, A_222) | ~v1_funct_1(B_223))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.21/3.40  tff(c_1440, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1433])).
% 9.21/3.40  tff(c_1455, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_1440])).
% 9.21/3.40  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_1459, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1455, c_68])).
% 9.21/3.40  tff(c_2070, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2068, c_1459])).
% 9.21/3.40  tff(c_2074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_508, c_2070])).
% 9.21/3.40  tff(c_2075, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_236])).
% 9.21/3.40  tff(c_2081, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2075, c_72])).
% 9.21/3.40  tff(c_3536, plain, (![A_452, B_453, D_454]: (r2_relset_1(A_452, B_453, D_454, D_454) | ~m1_subset_1(D_454, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.21/3.40  tff(c_3718, plain, (![D_475]: (r2_relset_1('#skF_1', '#skF_1', D_475, D_475) | ~m1_subset_1(D_475, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2075, c_3536])).
% 9.21/3.40  tff(c_3726, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2081, c_3718])).
% 9.21/3.40  tff(c_2080, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2075, c_80])).
% 9.21/3.40  tff(c_2163, plain, (![B_287, A_288]: (k2_relat_1(B_287)=A_288 | ~v2_funct_2(B_287, A_288) | ~v5_relat_1(B_287, A_288) | ~v1_relat_1(B_287))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.21/3.40  tff(c_2181, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_276, c_2163])).
% 9.21/3.40  tff(c_2195, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_2181])).
% 9.21/3.40  tff(c_2837, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_2195])).
% 9.21/3.40  tff(c_3137, plain, (![C_407, B_408, A_409]: (v2_funct_2(C_407, B_408) | ~v3_funct_2(C_407, A_409, B_408) | ~v1_funct_1(C_407) | ~m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.21/3.40  tff(c_3491, plain, (![C_449]: (v2_funct_2(C_449, '#skF_1') | ~v3_funct_2(C_449, '#skF_1', '#skF_1') | ~v1_funct_1(C_449) | ~m1_subset_1(C_449, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2075, c_3137])).
% 9.21/3.40  tff(c_3497, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2080, c_3491])).
% 9.21/3.40  tff(c_3507, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_3497])).
% 9.21/3.40  tff(c_3509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2837, c_3507])).
% 9.21/3.40  tff(c_3510, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_2195])).
% 9.21/3.40  tff(c_3637, plain, (![A_466, B_467, C_468]: (k2_relset_1(A_466, B_467, C_468)=k2_relat_1(C_468) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_466, B_467))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.21/3.40  tff(c_3777, plain, (![C_489]: (k2_relset_1('#skF_1', '#skF_1', C_489)=k2_relat_1(C_489) | ~m1_subset_1(C_489, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2075, c_3637])).
% 9.21/3.40  tff(c_3783, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2080, c_3777])).
% 9.21/3.40  tff(c_3791, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3510, c_3783])).
% 9.21/3.40  tff(c_3755, plain, (![C_480, A_481, B_482]: (v2_funct_1(C_480) | ~v3_funct_2(C_480, A_481, B_482) | ~v1_funct_1(C_480) | ~m1_subset_1(C_480, k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.21/3.40  tff(c_3914, plain, (![C_502]: (v2_funct_1(C_502) | ~v3_funct_2(C_502, '#skF_1', '#skF_1') | ~v1_funct_1(C_502) | ~m1_subset_1(C_502, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2075, c_3755])).
% 9.21/3.40  tff(c_3920, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2080, c_3914])).
% 9.21/3.40  tff(c_3930, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_3920])).
% 9.21/3.40  tff(c_5040, plain, (![C_625, D_626, B_627, A_628]: (k2_funct_1(C_625)=D_626 | k1_xboole_0=B_627 | k1_xboole_0=A_628 | ~v2_funct_1(C_625) | ~r2_relset_1(A_628, A_628, k1_partfun1(A_628, B_627, B_627, A_628, C_625, D_626), k6_partfun1(A_628)) | k2_relset_1(A_628, B_627, C_625)!=B_627 | ~m1_subset_1(D_626, k1_zfmisc_1(k2_zfmisc_1(B_627, A_628))) | ~v1_funct_2(D_626, B_627, A_628) | ~v1_funct_1(D_626) | ~m1_subset_1(C_625, k1_zfmisc_1(k2_zfmisc_1(A_628, B_627))) | ~v1_funct_2(C_625, A_628, B_627) | ~v1_funct_1(C_625))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.21/3.40  tff(c_5043, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_5040])).
% 9.21/3.40  tff(c_5049, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_2080, c_2075, c_78, c_76, c_2081, c_2075, c_3791, c_3930, c_5043])).
% 9.21/3.40  tff(c_5052, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_5049])).
% 9.21/3.40  tff(c_12, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.21/3.40  tff(c_2098, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2075, c_12])).
% 9.21/3.40  tff(c_2162, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_2098])).
% 9.21/3.40  tff(c_5076, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5052, c_2162])).
% 9.21/3.40  tff(c_5087, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5052, c_5052, c_14])).
% 9.21/3.40  tff(c_5332, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5087, c_2075])).
% 9.21/3.40  tff(c_5334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5076, c_5332])).
% 9.21/3.40  tff(c_5335, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_5049])).
% 9.21/3.40  tff(c_4118, plain, (![A_523, B_524]: (k2_funct_2(A_523, B_524)=k2_funct_1(B_524) | ~m1_subset_1(B_524, k1_zfmisc_1(k2_zfmisc_1(A_523, A_523))) | ~v3_funct_2(B_524, A_523, A_523) | ~v1_funct_2(B_524, A_523, A_523) | ~v1_funct_1(B_524))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.21/3.40  tff(c_4977, plain, (![B_619]: (k2_funct_2('#skF_1', B_619)=k2_funct_1(B_619) | ~m1_subset_1(B_619, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_619, '#skF_1', '#skF_1') | ~v1_funct_2(B_619, '#skF_1', '#skF_1') | ~v1_funct_1(B_619))), inference(superposition, [status(thm), theory('equality')], [c_2075, c_4118])).
% 9.21/3.40  tff(c_4983, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2080, c_4977])).
% 9.21/3.40  tff(c_4993, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_4983])).
% 9.21/3.40  tff(c_4999, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4993, c_68])).
% 9.21/3.40  tff(c_5337, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5335, c_4999])).
% 9.21/3.40  tff(c_5341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3726, c_5337])).
% 9.21/3.40  tff(c_5343, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2098])).
% 9.21/3.40  tff(c_5342, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2098])).
% 9.21/3.40  tff(c_5543, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5343, c_5343, c_5342])).
% 9.21/3.40  tff(c_5544, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_5543])).
% 9.21/3.40  tff(c_301, plain, (![A_78, B_79, A_80]: (v5_relat_1(A_78, B_79) | ~r1_tarski(A_78, k2_zfmisc_1(A_80, B_79)))), inference(resolution, [status(thm)], [c_20, c_258])).
% 9.21/3.40  tff(c_344, plain, (![A_83, B_84]: (v5_relat_1(k2_zfmisc_1(A_83, B_84), B_84))), inference(resolution, [status(thm)], [c_8, c_301])).
% 9.21/3.40  tff(c_350, plain, (![B_6]: (v5_relat_1(k1_xboole_0, B_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_344])).
% 9.21/3.40  tff(c_32, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.21/3.40  tff(c_160, plain, (![A_54]: (k2_relat_1(k6_partfun1(A_54))=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 9.21/3.40  tff(c_169, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_130, c_160])).
% 9.21/3.40  tff(c_2115, plain, (![B_285]: (v2_funct_2(B_285, k2_relat_1(B_285)) | ~v5_relat_1(B_285, k2_relat_1(B_285)) | ~v1_relat_1(B_285))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.21/3.40  tff(c_2126, plain, (v2_funct_2(k1_xboole_0, k2_relat_1(k1_xboole_0)) | ~v5_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_169, c_2115])).
% 9.21/3.40  tff(c_2135, plain, (v2_funct_2(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_350, c_169, c_2126])).
% 9.21/3.40  tff(c_5377, plain, (v2_funct_2('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5343, c_5343, c_2135])).
% 9.21/3.40  tff(c_5555, plain, (v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5544, c_5544, c_5377])).
% 9.21/3.40  tff(c_5387, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5343, c_5343, c_169])).
% 9.21/3.40  tff(c_5344, plain, (![B_637, A_638]: (k2_relat_1(B_637)=A_638 | ~v2_funct_2(B_637, A_638) | ~v5_relat_1(B_637, A_638) | ~v1_relat_1(B_637))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.21/3.40  tff(c_5362, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_276, c_5344])).
% 9.21/3.40  tff(c_5376, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_5362])).
% 9.21/3.40  tff(c_5482, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5387, c_5376])).
% 9.21/3.40  tff(c_5483, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_5482])).
% 9.21/3.40  tff(c_5547, plain, (~v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5544, c_5483])).
% 9.21/3.40  tff(c_5677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5555, c_5547])).
% 9.21/3.40  tff(c_5678, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_5543])).
% 9.21/3.40  tff(c_5679, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_5543])).
% 9.21/3.40  tff(c_5711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5678, c_5679])).
% 9.21/3.40  tff(c_5712, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_5482])).
% 9.21/3.40  tff(c_5726, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5712, c_5712, c_2080])).
% 9.21/3.40  tff(c_5723, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5712, c_5343])).
% 9.21/3.40  tff(c_407, plain, (![C_90, A_5]: (v4_relat_1(C_90, A_5) | ~m1_subset_1(C_90, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_394])).
% 9.21/3.40  tff(c_6060, plain, (![C_688, A_689]: (v4_relat_1(C_688, A_689) | ~m1_subset_1(C_688, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5723, c_407])).
% 9.21/3.40  tff(c_6068, plain, (![A_689]: (v4_relat_1('#skF_1', A_689))), inference(resolution, [status(thm)], [c_5726, c_6060])).
% 9.21/3.40  tff(c_5380, plain, (![A_82]: (r1_tarski('#skF_2', A_82) | ~v4_relat_1('#skF_2', A_82))), inference(demodulation, [status(thm), theory('equality')], [c_5343, c_5343, c_343])).
% 9.21/3.40  tff(c_5999, plain, (![A_82]: (r1_tarski('#skF_1', A_82) | ~v4_relat_1('#skF_1', A_82))), inference(demodulation, [status(thm), theory('equality')], [c_5712, c_5712, c_5380])).
% 9.21/3.40  tff(c_6072, plain, (![A_82]: (r1_tarski('#skF_1', A_82))), inference(demodulation, [status(thm), theory('equality')], [c_6068, c_5999])).
% 9.21/3.40  tff(c_211, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_203])).
% 9.21/3.40  tff(c_235, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_211, c_228])).
% 9.21/3.40  tff(c_353, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_235])).
% 9.21/3.40  tff(c_2077, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2075, c_353])).
% 9.21/3.40  tff(c_5727, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5712, c_2077])).
% 9.21/3.40  tff(c_6080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6072, c_5727])).
% 9.21/3.40  tff(c_6081, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_235])).
% 9.21/3.40  tff(c_6086, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6081, c_72])).
% 9.21/3.40  tff(c_10827, plain, (![A_1192, B_1193, D_1194]: (r2_relset_1(A_1192, B_1193, D_1194, D_1194) | ~m1_subset_1(D_1194, k1_zfmisc_1(k2_zfmisc_1(A_1192, B_1193))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.21/3.40  tff(c_10975, plain, (![D_1215]: (r2_relset_1('#skF_1', '#skF_1', D_1215, D_1215) | ~m1_subset_1(D_1215, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_10827])).
% 9.21/3.40  tff(c_10981, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_6086, c_10975])).
% 9.21/3.40  tff(c_74, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.21/3.40  tff(c_250, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_241])).
% 9.21/3.40  tff(c_257, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_250])).
% 9.21/3.40  tff(c_277, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_258])).
% 9.21/3.40  tff(c_10241, plain, (![B_1117, A_1118]: (k2_relat_1(B_1117)=A_1118 | ~v2_funct_2(B_1117, A_1118) | ~v5_relat_1(B_1117, A_1118) | ~v1_relat_1(B_1117))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.21/3.40  tff(c_10256, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_277, c_10241])).
% 9.21/3.40  tff(c_10267, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_10256])).
% 9.21/3.40  tff(c_10274, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_10267])).
% 9.21/3.40  tff(c_10636, plain, (![C_1172, B_1173, A_1174]: (v2_funct_2(C_1172, B_1173) | ~v3_funct_2(C_1172, A_1174, B_1173) | ~v1_funct_1(C_1172) | ~m1_subset_1(C_1172, k1_zfmisc_1(k2_zfmisc_1(A_1174, B_1173))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.21/3.40  tff(c_10792, plain, (![C_1190]: (v2_funct_2(C_1190, '#skF_1') | ~v3_funct_2(C_1190, '#skF_1', '#skF_1') | ~v1_funct_1(C_1190) | ~m1_subset_1(C_1190, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_10636])).
% 9.21/3.40  tff(c_10795, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6086, c_10792])).
% 9.21/3.40  tff(c_10802, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_10795])).
% 9.21/3.40  tff(c_10804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10274, c_10802])).
% 9.21/3.40  tff(c_10805, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_10267])).
% 9.21/3.40  tff(c_10938, plain, (![A_1209, B_1210, C_1211]: (k2_relset_1(A_1209, B_1210, C_1211)=k2_relat_1(C_1211) | ~m1_subset_1(C_1211, k1_zfmisc_1(k2_zfmisc_1(A_1209, B_1210))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.21/3.40  tff(c_11074, plain, (![C_1232]: (k2_relset_1('#skF_1', '#skF_1', C_1232)=k2_relat_1(C_1232) | ~m1_subset_1(C_1232, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_10938])).
% 9.21/3.40  tff(c_11077, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6086, c_11074])).
% 9.21/3.40  tff(c_11083, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10805, c_11077])).
% 9.21/3.40  tff(c_11012, plain, (![C_1222, A_1223, B_1224]: (v2_funct_1(C_1222) | ~v3_funct_2(C_1222, A_1223, B_1224) | ~v1_funct_1(C_1222) | ~m1_subset_1(C_1222, k1_zfmisc_1(k2_zfmisc_1(A_1223, B_1224))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.21/3.40  tff(c_11187, plain, (![C_1244]: (v2_funct_1(C_1244) | ~v3_funct_2(C_1244, '#skF_1', '#skF_1') | ~v1_funct_1(C_1244) | ~m1_subset_1(C_1244, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_11012])).
% 9.21/3.40  tff(c_11190, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6086, c_11187])).
% 9.21/3.40  tff(c_11197, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_11190])).
% 9.21/3.40  tff(c_7439, plain, (![A_846, B_847, D_848]: (r2_relset_1(A_846, B_847, D_848, D_848) | ~m1_subset_1(D_848, k1_zfmisc_1(k2_zfmisc_1(A_846, B_847))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.21/3.40  tff(c_7461, plain, (![D_855]: (r2_relset_1('#skF_1', '#skF_1', D_855, D_855) | ~m1_subset_1(D_855, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_7439])).
% 9.21/3.40  tff(c_7469, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_6086, c_7461])).
% 9.21/3.40  tff(c_6085, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6081, c_80])).
% 9.21/3.40  tff(c_6354, plain, (![B_718, A_719]: (k2_relat_1(B_718)=A_719 | ~v2_funct_2(B_718, A_719) | ~v5_relat_1(B_718, A_719) | ~v1_relat_1(B_718))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.21/3.40  tff(c_6372, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_276, c_6354])).
% 9.21/3.40  tff(c_6386, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_6372])).
% 9.21/3.40  tff(c_7008, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_6386])).
% 9.21/3.40  tff(c_7325, plain, (![C_836, B_837, A_838]: (v2_funct_2(C_836, B_837) | ~v3_funct_2(C_836, A_838, B_837) | ~v1_funct_1(C_836) | ~m1_subset_1(C_836, k1_zfmisc_1(k2_zfmisc_1(A_838, B_837))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.21/3.40  tff(c_7361, plain, (![C_843]: (v2_funct_2(C_843, '#skF_1') | ~v3_funct_2(C_843, '#skF_1', '#skF_1') | ~v1_funct_1(C_843) | ~m1_subset_1(C_843, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_7325])).
% 9.21/3.40  tff(c_7367, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_6085, c_7361])).
% 9.21/3.40  tff(c_7377, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_7367])).
% 9.21/3.40  tff(c_7379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7008, c_7377])).
% 9.21/3.40  tff(c_7380, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_6386])).
% 9.21/3.40  tff(c_7500, plain, (![A_860, B_861, C_862]: (k2_relset_1(A_860, B_861, C_862)=k2_relat_1(C_862) | ~m1_subset_1(C_862, k1_zfmisc_1(k2_zfmisc_1(A_860, B_861))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.21/3.40  tff(c_7577, plain, (![C_870]: (k2_relset_1('#skF_1', '#skF_1', C_870)=k2_relat_1(C_870) | ~m1_subset_1(C_870, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_7500])).
% 9.21/3.40  tff(c_7583, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6085, c_7577])).
% 9.21/3.40  tff(c_7591, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7380, c_7583])).
% 9.21/3.40  tff(c_7650, plain, (![C_876, A_877, B_878]: (v2_funct_1(C_876) | ~v3_funct_2(C_876, A_877, B_878) | ~v1_funct_1(C_876) | ~m1_subset_1(C_876, k1_zfmisc_1(k2_zfmisc_1(A_877, B_878))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.21/3.40  tff(c_7689, plain, (![C_883]: (v2_funct_1(C_883) | ~v3_funct_2(C_883, '#skF_1', '#skF_1') | ~v1_funct_1(C_883) | ~m1_subset_1(C_883, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_7650])).
% 9.21/3.40  tff(c_7695, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_6085, c_7689])).
% 9.21/3.40  tff(c_7705, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_7695])).
% 9.21/3.40  tff(c_9136, plain, (![C_1036, D_1037, B_1038, A_1039]: (k2_funct_1(C_1036)=D_1037 | k1_xboole_0=B_1038 | k1_xboole_0=A_1039 | ~v2_funct_1(C_1036) | ~r2_relset_1(A_1039, A_1039, k1_partfun1(A_1039, B_1038, B_1038, A_1039, C_1036, D_1037), k6_partfun1(A_1039)) | k2_relset_1(A_1039, B_1038, C_1036)!=B_1038 | ~m1_subset_1(D_1037, k1_zfmisc_1(k2_zfmisc_1(B_1038, A_1039))) | ~v1_funct_2(D_1037, B_1038, A_1039) | ~v1_funct_1(D_1037) | ~m1_subset_1(C_1036, k1_zfmisc_1(k2_zfmisc_1(A_1039, B_1038))) | ~v1_funct_2(C_1036, A_1039, B_1038) | ~v1_funct_1(C_1036))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.21/3.40  tff(c_9139, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_9136])).
% 9.21/3.40  tff(c_9145, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_6085, c_6081, c_78, c_76, c_6086, c_6081, c_7591, c_7705, c_9139])).
% 9.21/3.40  tff(c_9148, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_9145])).
% 9.21/3.40  tff(c_6100, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6081, c_12])).
% 9.21/3.40  tff(c_6170, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_6100])).
% 9.21/3.40  tff(c_9183, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9148, c_6170])).
% 9.21/3.40  tff(c_9193, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9148, c_9148, c_14])).
% 9.21/3.40  tff(c_9464, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9193, c_6081])).
% 9.21/3.40  tff(c_9466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9183, c_9464])).
% 9.21/3.40  tff(c_9467, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_9145])).
% 9.21/3.40  tff(c_8746, plain, (![A_994, B_995]: (k2_funct_2(A_994, B_995)=k2_funct_1(B_995) | ~m1_subset_1(B_995, k1_zfmisc_1(k2_zfmisc_1(A_994, A_994))) | ~v3_funct_2(B_995, A_994, A_994) | ~v1_funct_2(B_995, A_994, A_994) | ~v1_funct_1(B_995))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.21/3.40  tff(c_9074, plain, (![B_1032]: (k2_funct_2('#skF_1', B_1032)=k2_funct_1(B_1032) | ~m1_subset_1(B_1032, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_1032, '#skF_1', '#skF_1') | ~v1_funct_2(B_1032, '#skF_1', '#skF_1') | ~v1_funct_1(B_1032))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_8746])).
% 9.21/3.40  tff(c_9080, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_6085, c_9074])).
% 9.21/3.40  tff(c_9090, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_9080])).
% 9.21/3.40  tff(c_9096, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9090, c_68])).
% 9.21/3.40  tff(c_9470, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9467, c_9096])).
% 9.21/3.40  tff(c_9474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7469, c_9470])).
% 9.21/3.40  tff(c_9476, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_6100])).
% 9.21/3.40  tff(c_9475, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6100])).
% 9.21/3.40  tff(c_9614, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9476, c_9476, c_9475])).
% 9.21/3.40  tff(c_9615, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_9614])).
% 9.21/3.40  tff(c_9633, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9615, c_9615, c_6086])).
% 9.21/3.40  tff(c_9487, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9476, c_9476, c_14])).
% 9.21/3.40  tff(c_9765, plain, (![A_1067]: (k2_zfmisc_1(A_1067, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9615, c_9615, c_9487])).
% 9.21/3.40  tff(c_40, plain, (![C_20, A_18, B_19]: (v4_relat_1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.40  tff(c_10013, plain, (![C_1093, A_1094]: (v4_relat_1(C_1093, A_1094) | ~m1_subset_1(C_1093, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9765, c_40])).
% 9.21/3.40  tff(c_10022, plain, (![A_1094]: (v4_relat_1('#skF_1', A_1094))), inference(resolution, [status(thm)], [c_9633, c_10013])).
% 9.21/3.40  tff(c_9630, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9615, c_9476])).
% 9.21/3.40  tff(c_9907, plain, (![A_82]: (r1_tarski('#skF_1', A_82) | ~v4_relat_1('#skF_1', A_82))), inference(demodulation, [status(thm), theory('equality')], [c_9630, c_9630, c_343])).
% 9.21/3.40  tff(c_10041, plain, (![A_82]: (r1_tarski('#skF_1', A_82))), inference(demodulation, [status(thm), theory('equality')], [c_10022, c_9907])).
% 9.21/3.40  tff(c_6084, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6081, c_210])).
% 9.21/3.40  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.21/3.40  tff(c_6116, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6084, c_4])).
% 9.21/3.40  tff(c_6158, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_6116])).
% 9.21/3.40  tff(c_9632, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9615, c_6158])).
% 9.21/3.40  tff(c_10047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10041, c_9632])).
% 9.21/3.40  tff(c_10048, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_9614])).
% 9.21/3.40  tff(c_10049, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_9614])).
% 9.21/3.40  tff(c_10082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10048, c_10049])).
% 9.21/3.40  tff(c_10083, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_6116])).
% 9.21/3.40  tff(c_10089, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10083, c_70])).
% 9.21/3.40  tff(c_12499, plain, (![C_1388, D_1389, B_1390, A_1391]: (k2_funct_1(C_1388)=D_1389 | k1_xboole_0=B_1390 | k1_xboole_0=A_1391 | ~v2_funct_1(C_1388) | ~r2_relset_1(A_1391, A_1391, k1_partfun1(A_1391, B_1390, B_1390, A_1391, C_1388, D_1389), k6_partfun1(A_1391)) | k2_relset_1(A_1391, B_1390, C_1388)!=B_1390 | ~m1_subset_1(D_1389, k1_zfmisc_1(k2_zfmisc_1(B_1390, A_1391))) | ~v1_funct_2(D_1389, B_1390, A_1391) | ~v1_funct_1(D_1389) | ~m1_subset_1(C_1388, k1_zfmisc_1(k2_zfmisc_1(A_1391, B_1390))) | ~v1_funct_2(C_1388, A_1391, B_1390) | ~v1_funct_1(C_1388))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.21/3.40  tff(c_12502, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_10089, c_12499])).
% 9.21/3.40  tff(c_12508, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_6086, c_6081, c_11083, c_11197, c_12502])).
% 9.21/3.40  tff(c_12511, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_12508])).
% 9.21/3.40  tff(c_10131, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_6100])).
% 9.21/3.40  tff(c_12542, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12511, c_10131])).
% 9.21/3.40  tff(c_12554, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12511, c_12511, c_16])).
% 9.21/3.40  tff(c_12813, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12554, c_6081])).
% 9.21/3.40  tff(c_12815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12542, c_12813])).
% 9.21/3.40  tff(c_12816, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_12508])).
% 9.21/3.40  tff(c_12055, plain, (![A_1337, B_1338]: (k2_funct_2(A_1337, B_1338)=k2_funct_1(B_1338) | ~m1_subset_1(B_1338, k1_zfmisc_1(k2_zfmisc_1(A_1337, A_1337))) | ~v3_funct_2(B_1338, A_1337, A_1337) | ~v1_funct_2(B_1338, A_1337, A_1337) | ~v1_funct_1(B_1338))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.21/3.40  tff(c_12842, plain, (![B_1405]: (k2_funct_2('#skF_1', B_1405)=k2_funct_1(B_1405) | ~m1_subset_1(B_1405, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_1405, '#skF_1', '#skF_1') | ~v1_funct_2(B_1405, '#skF_1', '#skF_1') | ~v1_funct_1(B_1405))), inference(superposition, [status(thm), theory('equality')], [c_6081, c_12055])).
% 9.21/3.40  tff(c_12845, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6086, c_12842])).
% 9.21/3.40  tff(c_12852, plain, (k2_funct_2('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_12816, c_12845])).
% 9.21/3.40  tff(c_10090, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10083, c_68])).
% 9.21/3.40  tff(c_12854, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12852, c_10090])).
% 9.21/3.40  tff(c_12857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10981, c_12854])).
% 9.21/3.40  tff(c_12859, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_6100])).
% 9.21/3.40  tff(c_12858, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6100])).
% 9.21/3.40  tff(c_12991, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12859, c_12859, c_12858])).
% 9.21/3.40  tff(c_12992, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_12991])).
% 9.21/3.40  tff(c_13007, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12992, c_12992, c_6086])).
% 9.21/3.40  tff(c_13005, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12992, c_12859])).
% 9.21/3.40  tff(c_10115, plain, (![C_1101, A_1102, B_1103]: (v4_relat_1(C_1101, A_1102) | ~m1_subset_1(C_1101, k1_zfmisc_1(k2_zfmisc_1(A_1102, B_1103))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.21/3.40  tff(c_10125, plain, (![C_1101, A_5]: (v4_relat_1(C_1101, A_5) | ~m1_subset_1(C_1101, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_10115])).
% 9.21/3.40  tff(c_13302, plain, (![C_1438, A_1439]: (v4_relat_1(C_1438, A_1439) | ~m1_subset_1(C_1438, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_13005, c_10125])).
% 9.21/3.40  tff(c_13308, plain, (![A_1439]: (v4_relat_1('#skF_1', A_1439))), inference(resolution, [status(thm)], [c_13007, c_13302])).
% 9.21/3.40  tff(c_13239, plain, (![A_82]: (r1_tarski('#skF_1', A_82) | ~v4_relat_1('#skF_1', A_82))), inference(demodulation, [status(thm), theory('equality')], [c_13005, c_13005, c_343])).
% 9.21/3.40  tff(c_13312, plain, (![A_82]: (r1_tarski('#skF_1', A_82))), inference(demodulation, [status(thm), theory('equality')], [c_13308, c_13239])).
% 9.21/3.40  tff(c_12958, plain, (![A_1408, B_1409, D_1410]: (r2_relset_1(A_1408, B_1409, D_1410, D_1410) | ~m1_subset_1(D_1410, k1_zfmisc_1(k2_zfmisc_1(A_1408, B_1409))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.21/3.40  tff(c_13626, plain, (![A_1489, B_1490, A_1491]: (r2_relset_1(A_1489, B_1490, A_1491, A_1491) | ~r1_tarski(A_1491, k2_zfmisc_1(A_1489, B_1490)))), inference(resolution, [status(thm)], [c_20, c_12958])).
% 9.21/3.40  tff(c_13640, plain, (![A_1489, B_1490]: (r2_relset_1(A_1489, B_1490, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_13312, c_13626])).
% 9.21/3.40  tff(c_13011, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12992, c_76])).
% 9.21/3.40  tff(c_13010, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12992, c_74])).
% 9.21/3.40  tff(c_13012, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12992, c_78])).
% 9.21/3.40  tff(c_36, plain, (![A_17]: (k2_funct_1(k6_relat_1(A_17))=k6_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.21/3.40  tff(c_176, plain, (![A_55]: (k2_funct_1(k6_partfun1(A_55))=k6_partfun1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_36])).
% 9.21/3.40  tff(c_185, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_176])).
% 9.21/3.40  tff(c_188, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_130, c_185])).
% 9.21/3.40  tff(c_12867, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12859, c_12859, c_188])).
% 9.21/3.40  tff(c_12996, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12992, c_12992, c_12867])).
% 9.21/3.40  tff(c_13315, plain, (![A_1441, B_1442]: (k2_funct_2(A_1441, B_1442)=k2_funct_1(B_1442) | ~m1_subset_1(B_1442, k1_zfmisc_1(k2_zfmisc_1(A_1441, A_1441))) | ~v3_funct_2(B_1442, A_1441, A_1441) | ~v1_funct_2(B_1442, A_1441, A_1441) | ~v1_funct_1(B_1442))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.21/3.40  tff(c_14281, plain, (![A_1573, A_1574]: (k2_funct_2(A_1573, A_1574)=k2_funct_1(A_1574) | ~v3_funct_2(A_1574, A_1573, A_1573) | ~v1_funct_2(A_1574, A_1573, A_1573) | ~v1_funct_1(A_1574) | ~r1_tarski(A_1574, k2_zfmisc_1(A_1573, A_1573)))), inference(resolution, [status(thm)], [c_20, c_13315])).
% 9.21/3.40  tff(c_14285, plain, (![A_1573]: (k2_funct_2(A_1573, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1573, A_1573) | ~v1_funct_2('#skF_1', A_1573, A_1573) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_13312, c_14281])).
% 9.21/3.40  tff(c_14376, plain, (![A_1584]: (k2_funct_2(A_1584, '#skF_1')='#skF_1' | ~v3_funct_2('#skF_1', A_1584, A_1584) | ~v1_funct_2('#skF_1', A_1584, A_1584))), inference(demodulation, [status(thm), theory('equality')], [c_13012, c_12996, c_14285])).
% 9.21/3.40  tff(c_14379, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_13010, c_14376])).
% 9.21/3.40  tff(c_14382, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13011, c_14379])).
% 9.21/3.40  tff(c_12998, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12992, c_12992, c_10090])).
% 9.21/3.40  tff(c_14383, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14382, c_12998])).
% 9.21/3.40  tff(c_14386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13640, c_14383])).
% 9.21/3.40  tff(c_14387, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_12991])).
% 9.21/3.40  tff(c_14388, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_12991])).
% 9.21/3.40  tff(c_14420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14387, c_14388])).
% 9.21/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.21/3.40  
% 9.21/3.40  Inference rules
% 9.21/3.40  ----------------------
% 9.21/3.40  #Ref     : 0
% 9.21/3.40  #Sup     : 2927
% 9.21/3.40  #Fact    : 0
% 9.21/3.40  #Define  : 0
% 9.21/3.40  #Split   : 64
% 9.21/3.40  #Chain   : 0
% 9.21/3.40  #Close   : 0
% 9.21/3.40  
% 9.21/3.40  Ordering : KBO
% 9.21/3.40  
% 9.21/3.40  Simplification rules
% 9.21/3.40  ----------------------
% 9.21/3.40  #Subsume      : 483
% 9.21/3.40  #Demod        : 4062
% 9.21/3.40  #Tautology    : 1532
% 9.21/3.40  #SimpNegUnit  : 118
% 9.21/3.40  #BackRed      : 672
% 9.21/3.40  
% 9.21/3.40  #Partial instantiations: 0
% 9.21/3.40  #Strategies tried      : 1
% 9.21/3.40  
% 9.21/3.40  Timing (in seconds)
% 9.21/3.40  ----------------------
% 9.21/3.40  Preprocessing        : 0.35
% 9.21/3.40  Parsing              : 0.19
% 9.21/3.40  CNF conversion       : 0.02
% 9.21/3.40  Main loop            : 2.22
% 9.21/3.40  Inferencing          : 0.73
% 9.21/3.40  Reduction            : 0.82
% 9.21/3.40  Demodulation         : 0.60
% 9.21/3.40  BG Simplification    : 0.07
% 9.21/3.40  Subsumption          : 0.40
% 9.21/3.40  Abstraction          : 0.07
% 9.21/3.40  MUC search           : 0.00
% 9.21/3.40  Cooper               : 0.00
% 9.21/3.40  Total                : 2.67
% 9.21/3.40  Index Insertion      : 0.00
% 9.21/3.40  Index Deletion       : 0.00
% 9.21/3.40  Index Matching       : 0.00
% 9.21/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
