%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:57 EST 2020

% Result     : Theorem 8.25s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :  334 (4009 expanded)
%              Number of leaves         :   46 (1297 expanded)
%              Depth                    :   18
%              Number of atoms          :  649 (11793 expanded)
%              Number of equality atoms :  181 (2570 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_179,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_157,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_113,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_63,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_24,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_203,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_212,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_203])).

tff(c_219,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_212])).

tff(c_311,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_330,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_311])).

tff(c_7403,plain,(
    ! [B_746,A_747] :
      ( k2_relat_1(B_746) = A_747
      | ~ v2_funct_2(B_746,A_747)
      | ~ v5_relat_1(B_746,A_747)
      | ~ v1_relat_1(B_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7421,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_330,c_7403])).

tff(c_7433,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_7421])).

tff(c_7461,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7433])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_500,plain,(
    ! [A_102,B_103,D_104] :
      ( r2_relset_1(A_102,B_103,D_104,D_104)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_514,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_500])).

tff(c_82,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_80,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_76,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_209,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_203])).

tff(c_216,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_209])).

tff(c_329,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_311])).

tff(c_563,plain,(
    ! [B_111,A_112] :
      ( k2_relat_1(B_111) = A_112
      | ~ v2_funct_2(B_111,A_112)
      | ~ v5_relat_1(B_111,A_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_584,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_329,c_563])).

tff(c_601,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_584])).

tff(c_999,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_78,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1157,plain,(
    ! [C_168,B_169,A_170] :
      ( v2_funct_2(C_168,B_169)
      | ~ v3_funct_2(C_168,A_170,B_169)
      | ~ v1_funct_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1164,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1157])).

tff(c_1177,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1164])).

tff(c_1179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_999,c_1177])).

tff(c_1180,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_1266,plain,(
    ! [A_175,B_176,C_177] :
      ( k2_relset_1(A_175,B_176,C_177) = k2_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1273,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1266])).

tff(c_1285,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_1273])).

tff(c_1393,plain,(
    ! [C_184,A_185,B_186] :
      ( v2_funct_1(C_184)
      | ~ v3_funct_2(C_184,A_185,B_186)
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1400,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1393])).

tff(c_1413,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_1400])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1902,plain,(
    ! [C_251,D_252,B_253,A_254] :
      ( k2_funct_1(C_251) = D_252
      | k1_xboole_0 = B_253
      | k1_xboole_0 = A_254
      | ~ v2_funct_1(C_251)
      | ~ r2_relset_1(A_254,A_254,k1_partfun1(A_254,B_253,B_253,A_254,C_251,D_252),k6_partfun1(A_254))
      | k2_relset_1(A_254,B_253,C_251) != B_253
      | ~ m1_subset_1(D_252,k1_zfmisc_1(k2_zfmisc_1(B_253,A_254)))
      | ~ v1_funct_2(D_252,B_253,A_254)
      | ~ v1_funct_1(D_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_254,B_253)))
      | ~ v1_funct_2(C_251,A_254,B_253)
      | ~ v1_funct_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1905,plain,
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
    inference(resolution,[status(thm)],[c_66,c_1902])).

tff(c_1911,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_68,c_1285,c_1413,c_1905])).

tff(c_1914,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1911])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    ! [C_83,B_84] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_351,plain,(
    ! [A_85,B_86] :
      ( v5_relat_1(A_85,B_86)
      | ~ r1_tarski(A_85,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_346])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [A_48,B_49] : v1_relat_1(k2_zfmisc_1(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_129,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_135,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_30])).

tff(c_56,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_84,plain,(
    ! [A_14] : k2_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_28])).

tff(c_147,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_84])).

tff(c_261,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(k2_relat_1(B_66),A_67)
      | ~ v5_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_269,plain,(
    ! [A_67] :
      ( r1_tarski(k1_xboole_0,A_67)
      | ~ v5_relat_1(k1_xboole_0,A_67)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_261])).

tff(c_276,plain,(
    ! [A_67] :
      ( r1_tarski(k1_xboole_0,A_67)
      | ~ v5_relat_1(k1_xboole_0,A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_269])).

tff(c_355,plain,(
    ! [B_86] :
      ( r1_tarski(k1_xboole_0,B_86)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_351,c_276])).

tff(c_358,plain,(
    ! [B_86] : r1_tarski(k1_xboole_0,B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_355])).

tff(c_1938,plain,(
    ! [B_86] : r1_tarski('#skF_1',B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_358])).

tff(c_1950,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_1914,c_12])).

tff(c_190,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_201,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_190])).

tff(c_237,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_245,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_201,c_237])).

tff(c_415,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_2242,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1950,c_415])).

tff(c_2250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_2242])).

tff(c_2251,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1911])).

tff(c_1569,plain,(
    ! [A_215,B_216] :
      ( k2_funct_2(A_215,B_216) = k2_funct_1(B_216)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_zfmisc_1(A_215,A_215)))
      | ~ v3_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1576,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1569])).

tff(c_1591,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1576])).

tff(c_64,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1595,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_64])).

tff(c_2253,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2251,c_1595])).

tff(c_2257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_2253])).

tff(c_2258,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_2264,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2258,c_68])).

tff(c_2357,plain,(
    ! [A_270,B_271,D_272] :
      ( r2_relset_1(A_270,B_271,D_272,D_272)
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2401,plain,(
    ! [D_276] :
      ( r2_relset_1('#skF_1','#skF_1',D_276,D_276)
      | ~ m1_subset_1(D_276,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_2357])).

tff(c_2409,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2264,c_2401])).

tff(c_2263,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2258,c_76])).

tff(c_2444,plain,(
    ! [B_282,A_283] :
      ( k2_relat_1(B_282) = A_283
      | ~ v2_funct_2(B_282,A_283)
      | ~ v5_relat_1(B_282,A_283)
      | ~ v1_relat_1(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2465,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_329,c_2444])).

tff(c_2480,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_2465])).

tff(c_2825,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2480])).

tff(c_3055,plain,(
    ! [C_347,B_348,A_349] :
      ( v2_funct_2(C_347,B_348)
      | ~ v3_funct_2(C_347,A_349,B_348)
      | ~ v1_funct_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_349,B_348))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3076,plain,(
    ! [C_354] :
      ( v2_funct_2(C_354,'#skF_1')
      | ~ v3_funct_2(C_354,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_3055])).

tff(c_3082,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2263,c_3076])).

tff(c_3092,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_3082])).

tff(c_3094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2825,c_3092])).

tff(c_3095,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2480])).

tff(c_3158,plain,(
    ! [A_357,B_358,C_359] :
      ( k2_relset_1(A_357,B_358,C_359) = k2_relat_1(C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3210,plain,(
    ! [C_362] :
      ( k2_relset_1('#skF_1','#skF_1',C_362) = k2_relat_1(C_362)
      | ~ m1_subset_1(C_362,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_3158])).

tff(c_3216,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2263,c_3210])).

tff(c_3224,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3095,c_3216])).

tff(c_3235,plain,(
    ! [C_363,A_364,B_365] :
      ( v2_funct_1(C_363)
      | ~ v3_funct_2(C_363,A_364,B_365)
      | ~ v1_funct_1(C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3296,plain,(
    ! [C_372] :
      ( v2_funct_1(C_372)
      | ~ v3_funct_2(C_372,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_372)
      | ~ m1_subset_1(C_372,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_3235])).

tff(c_3302,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2263,c_3296])).

tff(c_3312,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_3302])).

tff(c_4033,plain,(
    ! [C_452,D_453,B_454,A_455] :
      ( k2_funct_1(C_452) = D_453
      | k1_xboole_0 = B_454
      | k1_xboole_0 = A_455
      | ~ v2_funct_1(C_452)
      | ~ r2_relset_1(A_455,A_455,k1_partfun1(A_455,B_454,B_454,A_455,C_452,D_453),k6_partfun1(A_455))
      | k2_relset_1(A_455,B_454,C_452) != B_454
      | ~ m1_subset_1(D_453,k1_zfmisc_1(k2_zfmisc_1(B_454,A_455)))
      | ~ v1_funct_2(D_453,B_454,A_455)
      | ~ v1_funct_1(D_453)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(A_455,B_454)))
      | ~ v1_funct_2(C_452,A_455,B_454)
      | ~ v1_funct_1(C_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_4036,plain,
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
    inference(resolution,[status(thm)],[c_66,c_4033])).

tff(c_4042,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2263,c_2258,c_74,c_72,c_2264,c_2258,c_3224,c_3312,c_4036])).

tff(c_4045,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4042])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2275,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_8])).

tff(c_2350,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2275])).

tff(c_4068,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4045,c_2350])).

tff(c_4084,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4045,c_4045,c_12])).

tff(c_4374,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4084,c_2258])).

tff(c_4376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4068,c_4374])).

tff(c_4377,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4042])).

tff(c_3608,plain,(
    ! [A_408,B_409] :
      ( k2_funct_2(A_408,B_409) = k2_funct_1(B_409)
      | ~ m1_subset_1(B_409,k1_zfmisc_1(k2_zfmisc_1(A_408,A_408)))
      | ~ v3_funct_2(B_409,A_408,A_408)
      | ~ v1_funct_2(B_409,A_408,A_408)
      | ~ v1_funct_1(B_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3785,plain,(
    ! [B_427] :
      ( k2_funct_2('#skF_1',B_427) = k2_funct_1(B_427)
      | ~ m1_subset_1(B_427,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_427,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_427,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_427) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_3608])).

tff(c_3791,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2263,c_3785])).

tff(c_3801,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_3791])).

tff(c_3807,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3801,c_64])).

tff(c_4379,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4377,c_3807])).

tff(c_4383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2409,c_4379])).

tff(c_4385,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2275])).

tff(c_4405,plain,(
    ! [B_86] : r1_tarski('#skF_2',B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4385,c_358])).

tff(c_202,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_190])).

tff(c_244,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_202,c_237])).

tff(c_337,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_2260,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2258,c_337])).

tff(c_4493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4405,c_2260])).

tff(c_4494,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_4499,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4494,c_68])).

tff(c_7821,plain,(
    ! [C_802,B_803,A_804] :
      ( v2_funct_2(C_802,B_803)
      | ~ v3_funct_2(C_802,A_804,B_803)
      | ~ v1_funct_1(C_802)
      | ~ m1_subset_1(C_802,k1_zfmisc_1(k2_zfmisc_1(A_804,B_803))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7870,plain,(
    ! [C_807] :
      ( v2_funct_2(C_807,'#skF_1')
      | ~ v3_funct_2(C_807,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_807)
      | ~ m1_subset_1(C_807,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_7821])).

tff(c_7873,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4499,c_7870])).

tff(c_7880,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_7873])).

tff(c_7882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7461,c_7880])).

tff(c_7883,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7433])).

tff(c_7946,plain,(
    ! [A_810,B_811,D_812] :
      ( r2_relset_1(A_810,B_811,D_812,D_812)
      | ~ m1_subset_1(D_812,k1_zfmisc_1(k2_zfmisc_1(A_810,B_811))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7984,plain,(
    ! [D_816] :
      ( r2_relset_1('#skF_1','#skF_1',D_816,D_816)
      | ~ m1_subset_1(D_816,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_7946])).

tff(c_7990,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_4499,c_7984])).

tff(c_8061,plain,(
    ! [A_822,B_823,C_824] :
      ( k2_relset_1(A_822,B_823,C_824) = k2_relat_1(C_824)
      | ~ m1_subset_1(C_824,k1_zfmisc_1(k2_zfmisc_1(A_822,B_823))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8102,plain,(
    ! [C_830] :
      ( k2_relset_1('#skF_1','#skF_1',C_830) = k2_relat_1(C_830)
      | ~ m1_subset_1(C_830,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_8061])).

tff(c_8105,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4499,c_8102])).

tff(c_8111,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7883,c_8105])).

tff(c_8141,plain,(
    ! [C_836,A_837,B_838] :
      ( v2_funct_1(C_836)
      | ~ v3_funct_2(C_836,A_837,B_838)
      | ~ v1_funct_1(C_836)
      | ~ m1_subset_1(C_836,k1_zfmisc_1(k2_zfmisc_1(A_837,B_838))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8192,plain,(
    ! [C_843] :
      ( v2_funct_1(C_843)
      | ~ v3_funct_2(C_843,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_843)
      | ~ m1_subset_1(C_843,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_8141])).

tff(c_8195,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4499,c_8192])).

tff(c_8202,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_8195])).

tff(c_4709,plain,(
    ! [A_490,B_491,D_492] :
      ( r2_relset_1(A_490,B_491,D_492,D_492)
      | ~ m1_subset_1(D_492,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4748,plain,(
    ! [D_496] :
      ( r2_relset_1('#skF_1','#skF_1',D_496,D_496)
      | ~ m1_subset_1(D_496,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_4709])).

tff(c_4756,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_4499,c_4748])).

tff(c_4498,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4494,c_76])).

tff(c_4799,plain,(
    ! [B_503,A_504] :
      ( k2_relat_1(B_503) = A_504
      | ~ v2_funct_2(B_503,A_504)
      | ~ v5_relat_1(B_503,A_504)
      | ~ v1_relat_1(B_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4823,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_329,c_4799])).

tff(c_4841,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_4823])).

tff(c_5175,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4841])).

tff(c_5398,plain,(
    ! [C_568,B_569,A_570] :
      ( v2_funct_2(C_568,B_569)
      | ~ v3_funct_2(C_568,A_570,B_569)
      | ~ v1_funct_1(C_568)
      | ~ m1_subset_1(C_568,k1_zfmisc_1(k2_zfmisc_1(A_570,B_569))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5420,plain,(
    ! [C_577] :
      ( v2_funct_2(C_577,'#skF_1')
      | ~ v3_funct_2(C_577,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_577)
      | ~ m1_subset_1(C_577,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_5398])).

tff(c_5426,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4498,c_5420])).

tff(c_5436,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_5426])).

tff(c_5438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5175,c_5436])).

tff(c_5439,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4841])).

tff(c_5502,plain,(
    ! [A_580,B_581,C_582] :
      ( k2_relset_1(A_580,B_581,C_582) = k2_relat_1(C_582)
      | ~ m1_subset_1(C_582,k1_zfmisc_1(k2_zfmisc_1(A_580,B_581))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5554,plain,(
    ! [C_585] :
      ( k2_relset_1('#skF_1','#skF_1',C_585) = k2_relat_1(C_585)
      | ~ m1_subset_1(C_585,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_5502])).

tff(c_5560,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4498,c_5554])).

tff(c_5568,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5439,c_5560])).

tff(c_5579,plain,(
    ! [C_586,A_587,B_588] :
      ( v2_funct_1(C_586)
      | ~ v3_funct_2(C_586,A_587,B_588)
      | ~ v1_funct_1(C_586)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(A_587,B_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5633,plain,(
    ! [C_595] :
      ( v2_funct_1(C_595)
      | ~ v3_funct_2(C_595,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_595)
      | ~ m1_subset_1(C_595,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_5579])).

tff(c_5639,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4498,c_5633])).

tff(c_5649,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_5639])).

tff(c_6350,plain,(
    ! [C_674,D_675,B_676,A_677] :
      ( k2_funct_1(C_674) = D_675
      | k1_xboole_0 = B_676
      | k1_xboole_0 = A_677
      | ~ v2_funct_1(C_674)
      | ~ r2_relset_1(A_677,A_677,k1_partfun1(A_677,B_676,B_676,A_677,C_674,D_675),k6_partfun1(A_677))
      | k2_relset_1(A_677,B_676,C_674) != B_676
      | ~ m1_subset_1(D_675,k1_zfmisc_1(k2_zfmisc_1(B_676,A_677)))
      | ~ v1_funct_2(D_675,B_676,A_677)
      | ~ v1_funct_1(D_675)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_zfmisc_1(A_677,B_676)))
      | ~ v1_funct_2(C_674,A_677,B_676)
      | ~ v1_funct_1(C_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6353,plain,
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
    inference(resolution,[status(thm)],[c_66,c_6350])).

tff(c_6359,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_4498,c_4494,c_74,c_72,c_4499,c_4494,c_5568,c_5649,c_6353])).

tff(c_6362,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6359])).

tff(c_4510,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_8])).

tff(c_4603,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4510])).

tff(c_6391,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_4603])).

tff(c_6400,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_6362,c_10])).

tff(c_6693,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6400,c_4494])).

tff(c_6695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6391,c_6693])).

tff(c_6696,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6359])).

tff(c_5929,plain,(
    ! [A_629,B_630] :
      ( k2_funct_2(A_629,B_630) = k2_funct_1(B_630)
      | ~ m1_subset_1(B_630,k1_zfmisc_1(k2_zfmisc_1(A_629,A_629)))
      | ~ v3_funct_2(B_630,A_629,A_629)
      | ~ v1_funct_2(B_630,A_629,A_629)
      | ~ v1_funct_1(B_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6118,plain,(
    ! [B_649] :
      ( k2_funct_2('#skF_1',B_649) = k2_funct_1(B_649)
      | ~ m1_subset_1(B_649,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_649,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_649,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_649) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_5929])).

tff(c_6124,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4498,c_6118])).

tff(c_6134,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_6124])).

tff(c_6140,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6134,c_64])).

tff(c_6698,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6696,c_6140])).

tff(c_6702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4756,c_6698])).

tff(c_6704,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4510])).

tff(c_6703,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4510])).

tff(c_6812,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6704,c_6704,c_6703])).

tff(c_6813,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6812])).

tff(c_6824,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6813,c_6813,c_4499])).

tff(c_6822,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6813,c_6704])).

tff(c_327,plain,(
    ! [C_78,B_4] :
      ( v5_relat_1(C_78,B_4)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_7116,plain,(
    ! [C_717,B_718] :
      ( v5_relat_1(C_717,B_718)
      | ~ m1_subset_1(C_717,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6822,c_327])).

tff(c_7124,plain,(
    ! [B_718] : v5_relat_1('#skF_1',B_718) ),
    inference(resolution,[status(thm)],[c_6824,c_7116])).

tff(c_6711,plain,(
    ! [A_67] :
      ( r1_tarski('#skF_3',A_67)
      | ~ v5_relat_1('#skF_3',A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6704,c_6704,c_276])).

tff(c_7058,plain,(
    ! [A_67] :
      ( r1_tarski('#skF_1',A_67)
      | ~ v5_relat_1('#skF_1',A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6813,c_6813,c_6711])).

tff(c_7128,plain,(
    ! [A_67] : r1_tarski('#skF_1',A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7124,c_7058])).

tff(c_4497,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4494,c_201])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4532,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4497,c_2])).

tff(c_4549,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4532])).

tff(c_6823,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6813,c_4549])).

tff(c_7148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7128,c_6823])).

tff(c_7149,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6812])).

tff(c_7150,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6812])).

tff(c_7185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7149,c_7150])).

tff(c_7186,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4532])).

tff(c_7193,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7186,c_66])).

tff(c_9115,plain,(
    ! [C_948,D_949,B_950,A_951] :
      ( k2_funct_1(C_948) = D_949
      | k1_xboole_0 = B_950
      | k1_xboole_0 = A_951
      | ~ v2_funct_1(C_948)
      | ~ r2_relset_1(A_951,A_951,k1_partfun1(A_951,B_950,B_950,A_951,C_948,D_949),k6_partfun1(A_951))
      | k2_relset_1(A_951,B_950,C_948) != B_950
      | ~ m1_subset_1(D_949,k1_zfmisc_1(k2_zfmisc_1(B_950,A_951)))
      | ~ v1_funct_2(D_949,B_950,A_951)
      | ~ v1_funct_1(D_949)
      | ~ m1_subset_1(C_948,k1_zfmisc_1(k2_zfmisc_1(A_951,B_950)))
      | ~ v1_funct_2(C_948,A_951,B_950)
      | ~ v1_funct_1(C_948) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_9118,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7193,c_9115])).

tff(c_9124,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4499,c_4494,c_8111,c_8202,c_9118])).

tff(c_9127,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9124])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( v5_relat_1(B_11,A_10)
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7894,plain,(
    ! [A_10] :
      ( v5_relat_1('#skF_3',A_10)
      | ~ r1_tarski('#skF_1',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7883,c_20])).

tff(c_7905,plain,(
    ! [A_10] :
      ( v5_relat_1('#skF_3',A_10)
      | ~ r1_tarski('#skF_1',A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_7894])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_278,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7378,plain,(
    ! [A_743,A_744,B_745] :
      ( v4_relat_1(A_743,A_744)
      | ~ r1_tarski(A_743,k2_zfmisc_1(A_744,B_745)) ) ),
    inference(resolution,[status(thm)],[c_16,c_278])).

tff(c_8989,plain,(
    ! [B_935,A_936,B_937] :
      ( v4_relat_1(k2_relat_1(B_935),A_936)
      | ~ v5_relat_1(B_935,k2_zfmisc_1(A_936,B_937))
      | ~ v1_relat_1(B_935) ) ),
    inference(resolution,[status(thm)],[c_22,c_7378])).

tff(c_9069,plain,(
    ! [B_946] :
      ( v4_relat_1(k2_relat_1(B_946),k1_xboole_0)
      | ~ v5_relat_1(B_946,k1_xboole_0)
      | ~ v1_relat_1(B_946) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8989])).

tff(c_9072,plain,
    ( v4_relat_1('#skF_1',k1_xboole_0)
    | ~ v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7883,c_9069])).

tff(c_9080,plain,
    ( v4_relat_1('#skF_1',k1_xboole_0)
    | ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_9072])).

tff(c_9097,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_9080])).

tff(c_9104,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7905,c_9097])).

tff(c_9129,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9127,c_9104])).

tff(c_9170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9129])).

tff(c_9171,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9124])).

tff(c_8497,plain,(
    ! [A_879,B_880] :
      ( k2_funct_2(A_879,B_880) = k2_funct_1(B_880)
      | ~ m1_subset_1(B_880,k1_zfmisc_1(k2_zfmisc_1(A_879,A_879)))
      | ~ v3_funct_2(B_880,A_879,A_879)
      | ~ v1_funct_2(B_880,A_879,A_879)
      | ~ v1_funct_1(B_880) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8941,plain,(
    ! [B_930] :
      ( k2_funct_2('#skF_1',B_930) = k2_funct_1(B_930)
      | ~ m1_subset_1(B_930,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_930,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_930,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_930) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4494,c_8497])).

tff(c_8944,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4499,c_8941])).

tff(c_8951,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_8944])).

tff(c_7194,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7186,c_64])).

tff(c_8953,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8951,c_7194])).

tff(c_9173,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9171,c_8953])).

tff(c_9177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7990,c_9173])).

tff(c_9179,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_9080])).

tff(c_7220,plain,(
    ! [C_725,B_726] :
      ( v5_relat_1(C_725,B_726)
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_7264,plain,(
    ! [A_730,B_731] :
      ( v5_relat_1(A_730,B_731)
      | ~ r1_tarski(A_730,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_7220])).

tff(c_7268,plain,(
    ! [B_731] :
      ( r1_tarski(k1_xboole_0,B_731)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7264,c_276])).

tff(c_7273,plain,(
    ! [B_732] : r1_tarski(k1_xboole_0,B_732) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7268])).

tff(c_7282,plain,(
    ! [B_733] :
      ( k1_xboole_0 = B_733
      | ~ r1_tarski(B_733,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7273,c_2])).

tff(c_7297,plain,(
    ! [B_11] :
      ( k2_relat_1(B_11) = k1_xboole_0
      | ~ v5_relat_1(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_7282])).

tff(c_9184,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9179,c_7297])).

tff(c_9196,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_7883,c_9184])).

tff(c_7219,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4510])).

tff(c_9228,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9196,c_7219])).

tff(c_9238,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9196,c_9196,c_12])).

tff(c_9522,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9238,c_4494])).

tff(c_9524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9228,c_9522])).

tff(c_9526,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4510])).

tff(c_9525,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4510])).

tff(c_9659,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9526,c_9526,c_9525])).

tff(c_9660,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9659])).

tff(c_9672,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9660,c_9660,c_4499])).

tff(c_9669,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9660,c_9526])).

tff(c_9930,plain,(
    ! [C_991,B_992] :
      ( v5_relat_1(C_991,B_992)
      | ~ m1_subset_1(C_991,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9669,c_327])).

tff(c_9936,plain,(
    ! [B_992] : v5_relat_1('#skF_1',B_992) ),
    inference(resolution,[status(thm)],[c_9672,c_9930])).

tff(c_9531,plain,(
    ! [A_67] :
      ( r1_tarski('#skF_3',A_67)
      | ~ v5_relat_1('#skF_3',A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9526,c_9526,c_276])).

tff(c_9871,plain,(
    ! [A_67] :
      ( r1_tarski('#skF_1',A_67)
      | ~ v5_relat_1('#skF_1',A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9660,c_9660,c_9531])).

tff(c_9940,plain,(
    ! [A_67] : r1_tarski('#skF_1',A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9936,c_9871])).

tff(c_9754,plain,(
    ! [A_973,B_974,D_975] :
      ( r2_relset_1(A_973,B_974,D_975,D_975)
      | ~ m1_subset_1(D_975,k1_zfmisc_1(k2_zfmisc_1(A_973,B_974))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10314,plain,(
    ! [A_1051,B_1052,A_1053] :
      ( r2_relset_1(A_1051,B_1052,A_1053,A_1053)
      | ~ r1_tarski(A_1053,k2_zfmisc_1(A_1051,B_1052)) ) ),
    inference(resolution,[status(thm)],[c_16,c_9754])).

tff(c_10328,plain,(
    ! [A_1051,B_1052] : r2_relset_1(A_1051,B_1052,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_9940,c_10314])).

tff(c_9677,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9660,c_72])).

tff(c_9678,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9660,c_70])).

tff(c_9679,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9660,c_74])).

tff(c_32,plain,(
    ! [A_15] : k2_funct_1(k6_relat_1(A_15)) = k6_relat_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_172,plain,(
    ! [A_53] : k2_funct_1(k6_partfun1(A_53)) = k6_partfun1(A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_32])).

tff(c_181,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_172])).

tff(c_184,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_181])).

tff(c_9533,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9526,c_9526,c_184])).

tff(c_9668,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9660,c_9660,c_9533])).

tff(c_10085,plain,(
    ! [A_1015,B_1016] :
      ( k2_funct_2(A_1015,B_1016) = k2_funct_1(B_1016)
      | ~ m1_subset_1(B_1016,k1_zfmisc_1(k2_zfmisc_1(A_1015,A_1015)))
      | ~ v3_funct_2(B_1016,A_1015,A_1015)
      | ~ v1_funct_2(B_1016,A_1015,A_1015)
      | ~ v1_funct_1(B_1016) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_11041,plain,(
    ! [A_1150,A_1151] :
      ( k2_funct_2(A_1150,A_1151) = k2_funct_1(A_1151)
      | ~ v3_funct_2(A_1151,A_1150,A_1150)
      | ~ v1_funct_2(A_1151,A_1150,A_1150)
      | ~ v1_funct_1(A_1151)
      | ~ r1_tarski(A_1151,k2_zfmisc_1(A_1150,A_1150)) ) ),
    inference(resolution,[status(thm)],[c_16,c_10085])).

tff(c_11045,plain,(
    ! [A_1150] :
      ( k2_funct_2(A_1150,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_1150,A_1150)
      | ~ v1_funct_2('#skF_1',A_1150,A_1150)
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_9940,c_11041])).

tff(c_11074,plain,(
    ! [A_1153] :
      ( k2_funct_2(A_1153,'#skF_1') = '#skF_1'
      | ~ v3_funct_2('#skF_1',A_1153,A_1153)
      | ~ v1_funct_2('#skF_1',A_1153,A_1153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9679,c_9668,c_11045])).

tff(c_11077,plain,
    ( k2_funct_2('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_9678,c_11074])).

tff(c_11080,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9677,c_11077])).

tff(c_9670,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9660,c_9660,c_7194])).

tff(c_11081,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11080,c_9670])).

tff(c_11084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10328,c_11081])).

tff(c_11085,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9659])).

tff(c_11086,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9659])).

tff(c_11113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11085,c_11086])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.25/2.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.25/2.90  
% 8.25/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.25/2.90  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.25/2.90  
% 8.25/2.90  %Foreground sorts:
% 8.25/2.90  
% 8.25/2.90  
% 8.25/2.90  %Background operators:
% 8.25/2.90  
% 8.25/2.90  
% 8.25/2.90  %Foreground operators:
% 8.25/2.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.25/2.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.25/2.90  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.25/2.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.25/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.25/2.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.25/2.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.25/2.90  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 8.25/2.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.25/2.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.25/2.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.25/2.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.25/2.90  tff('#skF_2', type, '#skF_2': $i).
% 8.25/2.90  tff('#skF_3', type, '#skF_3': $i).
% 8.25/2.90  tff('#skF_1', type, '#skF_1': $i).
% 8.25/2.90  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.25/2.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.25/2.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.25/2.90  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.25/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.25/2.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.25/2.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.25/2.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.25/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.25/2.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.25/2.90  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.25/2.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.25/2.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.25/2.90  
% 8.55/2.94  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.55/2.94  tff(f_179, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 8.55/2.94  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.55/2.94  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.55/2.94  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 8.55/2.94  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.55/2.94  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.55/2.94  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.55/2.94  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 8.55/2.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.55/2.94  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.55/2.94  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.55/2.94  tff(f_113, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.55/2.94  tff(f_61, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 8.55/2.94  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.55/2.94  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.55/2.94  tff(f_111, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 8.55/2.94  tff(f_63, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 8.55/2.94  tff(c_24, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.55/2.94  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_203, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.55/2.94  tff(c_212, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_203])).
% 8.55/2.94  tff(c_219, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_212])).
% 8.55/2.94  tff(c_311, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.55/2.94  tff(c_330, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_311])).
% 8.55/2.94  tff(c_7403, plain, (![B_746, A_747]: (k2_relat_1(B_746)=A_747 | ~v2_funct_2(B_746, A_747) | ~v5_relat_1(B_746, A_747) | ~v1_relat_1(B_746))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.55/2.94  tff(c_7421, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_330, c_7403])).
% 8.55/2.94  tff(c_7433, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_7421])).
% 8.55/2.94  tff(c_7461, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_7433])).
% 8.55/2.94  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_70, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_500, plain, (![A_102, B_103, D_104]: (r2_relset_1(A_102, B_103, D_104, D_104) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.55/2.94  tff(c_514, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_500])).
% 8.55/2.94  tff(c_82, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_80, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_76, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_209, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_203])).
% 8.55/2.94  tff(c_216, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_209])).
% 8.55/2.94  tff(c_329, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_311])).
% 8.55/2.94  tff(c_563, plain, (![B_111, A_112]: (k2_relat_1(B_111)=A_112 | ~v2_funct_2(B_111, A_112) | ~v5_relat_1(B_111, A_112) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.55/2.94  tff(c_584, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_329, c_563])).
% 8.55/2.94  tff(c_601, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_584])).
% 8.55/2.94  tff(c_999, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_601])).
% 8.55/2.94  tff(c_78, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_1157, plain, (![C_168, B_169, A_170]: (v2_funct_2(C_168, B_169) | ~v3_funct_2(C_168, A_170, B_169) | ~v1_funct_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.94  tff(c_1164, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1157])).
% 8.55/2.94  tff(c_1177, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1164])).
% 8.55/2.94  tff(c_1179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_999, c_1177])).
% 8.55/2.94  tff(c_1180, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_601])).
% 8.55/2.94  tff(c_1266, plain, (![A_175, B_176, C_177]: (k2_relset_1(A_175, B_176, C_177)=k2_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.55/2.94  tff(c_1273, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1266])).
% 8.55/2.94  tff(c_1285, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1180, c_1273])).
% 8.55/2.94  tff(c_1393, plain, (![C_184, A_185, B_186]: (v2_funct_1(C_184) | ~v3_funct_2(C_184, A_185, B_186) | ~v1_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.94  tff(c_1400, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1393])).
% 8.55/2.94  tff(c_1413, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_1400])).
% 8.55/2.94  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_1902, plain, (![C_251, D_252, B_253, A_254]: (k2_funct_1(C_251)=D_252 | k1_xboole_0=B_253 | k1_xboole_0=A_254 | ~v2_funct_1(C_251) | ~r2_relset_1(A_254, A_254, k1_partfun1(A_254, B_253, B_253, A_254, C_251, D_252), k6_partfun1(A_254)) | k2_relset_1(A_254, B_253, C_251)!=B_253 | ~m1_subset_1(D_252, k1_zfmisc_1(k2_zfmisc_1(B_253, A_254))) | ~v1_funct_2(D_252, B_253, A_254) | ~v1_funct_1(D_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_254, B_253))) | ~v1_funct_2(C_251, A_254, B_253) | ~v1_funct_1(C_251))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.55/2.94  tff(c_1905, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1902])).
% 8.55/2.94  tff(c_1911, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_68, c_1285, c_1413, c_1905])).
% 8.55/2.94  tff(c_1914, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1911])).
% 8.55/2.94  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/2.94  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.55/2.94  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.55/2.94  tff(c_346, plain, (![C_83, B_84]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_311])).
% 8.55/2.94  tff(c_351, plain, (![A_85, B_86]: (v5_relat_1(A_85, B_86) | ~r1_tarski(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_346])).
% 8.55/2.94  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.55/2.94  tff(c_114, plain, (![A_48, B_49]: (v1_relat_1(k2_zfmisc_1(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.55/2.94  tff(c_116, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_114])).
% 8.55/2.94  tff(c_129, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.55/2.94  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.55/2.94  tff(c_135, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_129, c_30])).
% 8.55/2.94  tff(c_56, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.55/2.94  tff(c_28, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/2.94  tff(c_84, plain, (![A_14]: (k2_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_28])).
% 8.55/2.94  tff(c_147, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_135, c_84])).
% 8.55/2.94  tff(c_261, plain, (![B_66, A_67]: (r1_tarski(k2_relat_1(B_66), A_67) | ~v5_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.55/2.94  tff(c_269, plain, (![A_67]: (r1_tarski(k1_xboole_0, A_67) | ~v5_relat_1(k1_xboole_0, A_67) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_147, c_261])).
% 8.55/2.94  tff(c_276, plain, (![A_67]: (r1_tarski(k1_xboole_0, A_67) | ~v5_relat_1(k1_xboole_0, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_269])).
% 8.55/2.94  tff(c_355, plain, (![B_86]: (r1_tarski(k1_xboole_0, B_86) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_351, c_276])).
% 8.55/2.94  tff(c_358, plain, (![B_86]: (r1_tarski(k1_xboole_0, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_355])).
% 8.55/2.94  tff(c_1938, plain, (![B_86]: (r1_tarski('#skF_1', B_86))), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_358])).
% 8.55/2.94  tff(c_1950, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_1914, c_12])).
% 8.55/2.94  tff(c_190, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.55/2.94  tff(c_201, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_190])).
% 8.55/2.94  tff(c_237, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/2.94  tff(c_245, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_201, c_237])).
% 8.55/2.94  tff(c_415, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_245])).
% 8.55/2.94  tff(c_2242, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1950, c_415])).
% 8.55/2.94  tff(c_2250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1938, c_2242])).
% 8.55/2.94  tff(c_2251, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1911])).
% 8.55/2.94  tff(c_1569, plain, (![A_215, B_216]: (k2_funct_2(A_215, B_216)=k2_funct_1(B_216) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_zfmisc_1(A_215, A_215))) | ~v3_funct_2(B_216, A_215, A_215) | ~v1_funct_2(B_216, A_215, A_215) | ~v1_funct_1(B_216))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.55/2.94  tff(c_1576, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1569])).
% 8.55/2.94  tff(c_1591, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1576])).
% 8.55/2.94  tff(c_64, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.55/2.94  tff(c_1595, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_64])).
% 8.55/2.94  tff(c_2253, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2251, c_1595])).
% 8.55/2.94  tff(c_2257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_2253])).
% 8.55/2.94  tff(c_2258, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_245])).
% 8.55/2.94  tff(c_2264, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2258, c_68])).
% 8.55/2.94  tff(c_2357, plain, (![A_270, B_271, D_272]: (r2_relset_1(A_270, B_271, D_272, D_272) | ~m1_subset_1(D_272, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.55/2.94  tff(c_2401, plain, (![D_276]: (r2_relset_1('#skF_1', '#skF_1', D_276, D_276) | ~m1_subset_1(D_276, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_2357])).
% 8.55/2.94  tff(c_2409, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2264, c_2401])).
% 8.55/2.94  tff(c_2263, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2258, c_76])).
% 8.55/2.94  tff(c_2444, plain, (![B_282, A_283]: (k2_relat_1(B_282)=A_283 | ~v2_funct_2(B_282, A_283) | ~v5_relat_1(B_282, A_283) | ~v1_relat_1(B_282))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.55/2.94  tff(c_2465, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_329, c_2444])).
% 8.55/2.94  tff(c_2480, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_2465])).
% 8.55/2.94  tff(c_2825, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_2480])).
% 8.55/2.94  tff(c_3055, plain, (![C_347, B_348, A_349]: (v2_funct_2(C_347, B_348) | ~v3_funct_2(C_347, A_349, B_348) | ~v1_funct_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_349, B_348))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.94  tff(c_3076, plain, (![C_354]: (v2_funct_2(C_354, '#skF_1') | ~v3_funct_2(C_354, '#skF_1', '#skF_1') | ~v1_funct_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_3055])).
% 8.55/2.94  tff(c_3082, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2263, c_3076])).
% 8.55/2.94  tff(c_3092, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_3082])).
% 8.55/2.94  tff(c_3094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2825, c_3092])).
% 8.55/2.94  tff(c_3095, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_2480])).
% 8.55/2.94  tff(c_3158, plain, (![A_357, B_358, C_359]: (k2_relset_1(A_357, B_358, C_359)=k2_relat_1(C_359) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.55/2.94  tff(c_3210, plain, (![C_362]: (k2_relset_1('#skF_1', '#skF_1', C_362)=k2_relat_1(C_362) | ~m1_subset_1(C_362, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_3158])).
% 8.55/2.94  tff(c_3216, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2263, c_3210])).
% 8.55/2.94  tff(c_3224, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3095, c_3216])).
% 8.55/2.94  tff(c_3235, plain, (![C_363, A_364, B_365]: (v2_funct_1(C_363) | ~v3_funct_2(C_363, A_364, B_365) | ~v1_funct_1(C_363) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.94  tff(c_3296, plain, (![C_372]: (v2_funct_1(C_372) | ~v3_funct_2(C_372, '#skF_1', '#skF_1') | ~v1_funct_1(C_372) | ~m1_subset_1(C_372, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_3235])).
% 8.55/2.94  tff(c_3302, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2263, c_3296])).
% 8.55/2.94  tff(c_3312, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_3302])).
% 8.55/2.94  tff(c_4033, plain, (![C_452, D_453, B_454, A_455]: (k2_funct_1(C_452)=D_453 | k1_xboole_0=B_454 | k1_xboole_0=A_455 | ~v2_funct_1(C_452) | ~r2_relset_1(A_455, A_455, k1_partfun1(A_455, B_454, B_454, A_455, C_452, D_453), k6_partfun1(A_455)) | k2_relset_1(A_455, B_454, C_452)!=B_454 | ~m1_subset_1(D_453, k1_zfmisc_1(k2_zfmisc_1(B_454, A_455))) | ~v1_funct_2(D_453, B_454, A_455) | ~v1_funct_1(D_453) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(A_455, B_454))) | ~v1_funct_2(C_452, A_455, B_454) | ~v1_funct_1(C_452))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.55/2.94  tff(c_4036, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_4033])).
% 8.55/2.94  tff(c_4042, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2263, c_2258, c_74, c_72, c_2264, c_2258, c_3224, c_3312, c_4036])).
% 8.55/2.94  tff(c_4045, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_4042])).
% 8.55/2.94  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.55/2.94  tff(c_2275, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2258, c_8])).
% 8.55/2.94  tff(c_2350, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_2275])).
% 8.55/2.94  tff(c_4068, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4045, c_2350])).
% 8.55/2.94  tff(c_4084, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4045, c_4045, c_12])).
% 8.55/2.94  tff(c_4374, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4084, c_2258])).
% 8.55/2.94  tff(c_4376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4068, c_4374])).
% 8.55/2.94  tff(c_4377, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_4042])).
% 8.55/2.94  tff(c_3608, plain, (![A_408, B_409]: (k2_funct_2(A_408, B_409)=k2_funct_1(B_409) | ~m1_subset_1(B_409, k1_zfmisc_1(k2_zfmisc_1(A_408, A_408))) | ~v3_funct_2(B_409, A_408, A_408) | ~v1_funct_2(B_409, A_408, A_408) | ~v1_funct_1(B_409))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.55/2.94  tff(c_3785, plain, (![B_427]: (k2_funct_2('#skF_1', B_427)=k2_funct_1(B_427) | ~m1_subset_1(B_427, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_427, '#skF_1', '#skF_1') | ~v1_funct_2(B_427, '#skF_1', '#skF_1') | ~v1_funct_1(B_427))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_3608])).
% 8.55/2.94  tff(c_3791, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2263, c_3785])).
% 8.55/2.94  tff(c_3801, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_3791])).
% 8.55/2.94  tff(c_3807, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3801, c_64])).
% 8.55/2.94  tff(c_4379, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4377, c_3807])).
% 8.55/2.94  tff(c_4383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2409, c_4379])).
% 8.55/2.94  tff(c_4385, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2275])).
% 8.55/2.94  tff(c_4405, plain, (![B_86]: (r1_tarski('#skF_2', B_86))), inference(demodulation, [status(thm), theory('equality')], [c_4385, c_358])).
% 8.55/2.94  tff(c_202, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_190])).
% 8.55/2.94  tff(c_244, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_202, c_237])).
% 8.55/2.94  tff(c_337, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_244])).
% 8.55/2.94  tff(c_2260, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2258, c_337])).
% 8.55/2.94  tff(c_4493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4405, c_2260])).
% 8.55/2.94  tff(c_4494, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_244])).
% 8.55/2.94  tff(c_4499, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4494, c_68])).
% 8.55/2.94  tff(c_7821, plain, (![C_802, B_803, A_804]: (v2_funct_2(C_802, B_803) | ~v3_funct_2(C_802, A_804, B_803) | ~v1_funct_1(C_802) | ~m1_subset_1(C_802, k1_zfmisc_1(k2_zfmisc_1(A_804, B_803))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.94  tff(c_7870, plain, (![C_807]: (v2_funct_2(C_807, '#skF_1') | ~v3_funct_2(C_807, '#skF_1', '#skF_1') | ~v1_funct_1(C_807) | ~m1_subset_1(C_807, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_7821])).
% 8.55/2.94  tff(c_7873, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4499, c_7870])).
% 8.55/2.94  tff(c_7880, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_7873])).
% 8.55/2.94  tff(c_7882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7461, c_7880])).
% 8.55/2.94  tff(c_7883, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_7433])).
% 8.55/2.94  tff(c_7946, plain, (![A_810, B_811, D_812]: (r2_relset_1(A_810, B_811, D_812, D_812) | ~m1_subset_1(D_812, k1_zfmisc_1(k2_zfmisc_1(A_810, B_811))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.55/2.94  tff(c_7984, plain, (![D_816]: (r2_relset_1('#skF_1', '#skF_1', D_816, D_816) | ~m1_subset_1(D_816, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_7946])).
% 8.55/2.94  tff(c_7990, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_4499, c_7984])).
% 8.55/2.94  tff(c_8061, plain, (![A_822, B_823, C_824]: (k2_relset_1(A_822, B_823, C_824)=k2_relat_1(C_824) | ~m1_subset_1(C_824, k1_zfmisc_1(k2_zfmisc_1(A_822, B_823))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.55/2.94  tff(c_8102, plain, (![C_830]: (k2_relset_1('#skF_1', '#skF_1', C_830)=k2_relat_1(C_830) | ~m1_subset_1(C_830, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_8061])).
% 8.55/2.94  tff(c_8105, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4499, c_8102])).
% 8.55/2.94  tff(c_8111, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7883, c_8105])).
% 8.55/2.94  tff(c_8141, plain, (![C_836, A_837, B_838]: (v2_funct_1(C_836) | ~v3_funct_2(C_836, A_837, B_838) | ~v1_funct_1(C_836) | ~m1_subset_1(C_836, k1_zfmisc_1(k2_zfmisc_1(A_837, B_838))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.94  tff(c_8192, plain, (![C_843]: (v2_funct_1(C_843) | ~v3_funct_2(C_843, '#skF_1', '#skF_1') | ~v1_funct_1(C_843) | ~m1_subset_1(C_843, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_8141])).
% 8.55/2.94  tff(c_8195, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4499, c_8192])).
% 8.55/2.94  tff(c_8202, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_8195])).
% 8.55/2.94  tff(c_4709, plain, (![A_490, B_491, D_492]: (r2_relset_1(A_490, B_491, D_492, D_492) | ~m1_subset_1(D_492, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.55/2.94  tff(c_4748, plain, (![D_496]: (r2_relset_1('#skF_1', '#skF_1', D_496, D_496) | ~m1_subset_1(D_496, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_4709])).
% 8.55/2.94  tff(c_4756, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_4499, c_4748])).
% 8.55/2.94  tff(c_4498, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4494, c_76])).
% 8.55/2.94  tff(c_4799, plain, (![B_503, A_504]: (k2_relat_1(B_503)=A_504 | ~v2_funct_2(B_503, A_504) | ~v5_relat_1(B_503, A_504) | ~v1_relat_1(B_503))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.55/2.94  tff(c_4823, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_329, c_4799])).
% 8.55/2.94  tff(c_4841, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_4823])).
% 8.55/2.94  tff(c_5175, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4841])).
% 8.55/2.94  tff(c_5398, plain, (![C_568, B_569, A_570]: (v2_funct_2(C_568, B_569) | ~v3_funct_2(C_568, A_570, B_569) | ~v1_funct_1(C_568) | ~m1_subset_1(C_568, k1_zfmisc_1(k2_zfmisc_1(A_570, B_569))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.94  tff(c_5420, plain, (![C_577]: (v2_funct_2(C_577, '#skF_1') | ~v3_funct_2(C_577, '#skF_1', '#skF_1') | ~v1_funct_1(C_577) | ~m1_subset_1(C_577, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_5398])).
% 8.55/2.94  tff(c_5426, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_4498, c_5420])).
% 8.55/2.94  tff(c_5436, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_5426])).
% 8.55/2.94  tff(c_5438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5175, c_5436])).
% 8.55/2.94  tff(c_5439, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4841])).
% 8.55/2.94  tff(c_5502, plain, (![A_580, B_581, C_582]: (k2_relset_1(A_580, B_581, C_582)=k2_relat_1(C_582) | ~m1_subset_1(C_582, k1_zfmisc_1(k2_zfmisc_1(A_580, B_581))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.55/2.94  tff(c_5554, plain, (![C_585]: (k2_relset_1('#skF_1', '#skF_1', C_585)=k2_relat_1(C_585) | ~m1_subset_1(C_585, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_5502])).
% 8.55/2.94  tff(c_5560, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4498, c_5554])).
% 8.55/2.94  tff(c_5568, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5439, c_5560])).
% 8.55/2.94  tff(c_5579, plain, (![C_586, A_587, B_588]: (v2_funct_1(C_586) | ~v3_funct_2(C_586, A_587, B_588) | ~v1_funct_1(C_586) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(A_587, B_588))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.55/2.94  tff(c_5633, plain, (![C_595]: (v2_funct_1(C_595) | ~v3_funct_2(C_595, '#skF_1', '#skF_1') | ~v1_funct_1(C_595) | ~m1_subset_1(C_595, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_5579])).
% 8.55/2.94  tff(c_5639, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_4498, c_5633])).
% 8.55/2.94  tff(c_5649, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_5639])).
% 8.55/2.94  tff(c_6350, plain, (![C_674, D_675, B_676, A_677]: (k2_funct_1(C_674)=D_675 | k1_xboole_0=B_676 | k1_xboole_0=A_677 | ~v2_funct_1(C_674) | ~r2_relset_1(A_677, A_677, k1_partfun1(A_677, B_676, B_676, A_677, C_674, D_675), k6_partfun1(A_677)) | k2_relset_1(A_677, B_676, C_674)!=B_676 | ~m1_subset_1(D_675, k1_zfmisc_1(k2_zfmisc_1(B_676, A_677))) | ~v1_funct_2(D_675, B_676, A_677) | ~v1_funct_1(D_675) | ~m1_subset_1(C_674, k1_zfmisc_1(k2_zfmisc_1(A_677, B_676))) | ~v1_funct_2(C_674, A_677, B_676) | ~v1_funct_1(C_674))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.55/2.94  tff(c_6353, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_6350])).
% 8.55/2.94  tff(c_6359, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_4498, c_4494, c_74, c_72, c_4499, c_4494, c_5568, c_5649, c_6353])).
% 8.55/2.94  tff(c_6362, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_6359])).
% 8.55/2.94  tff(c_4510, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4494, c_8])).
% 8.55/2.94  tff(c_4603, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_4510])).
% 8.55/2.94  tff(c_6391, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6362, c_4603])).
% 8.55/2.94  tff(c_6400, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6362, c_6362, c_10])).
% 8.55/2.94  tff(c_6693, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6400, c_4494])).
% 8.55/2.94  tff(c_6695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6391, c_6693])).
% 8.55/2.94  tff(c_6696, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_6359])).
% 8.55/2.94  tff(c_5929, plain, (![A_629, B_630]: (k2_funct_2(A_629, B_630)=k2_funct_1(B_630) | ~m1_subset_1(B_630, k1_zfmisc_1(k2_zfmisc_1(A_629, A_629))) | ~v3_funct_2(B_630, A_629, A_629) | ~v1_funct_2(B_630, A_629, A_629) | ~v1_funct_1(B_630))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.55/2.94  tff(c_6118, plain, (![B_649]: (k2_funct_2('#skF_1', B_649)=k2_funct_1(B_649) | ~m1_subset_1(B_649, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_649, '#skF_1', '#skF_1') | ~v1_funct_2(B_649, '#skF_1', '#skF_1') | ~v1_funct_1(B_649))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_5929])).
% 8.55/2.94  tff(c_6124, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_4498, c_6118])).
% 8.55/2.94  tff(c_6134, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_6124])).
% 8.55/2.94  tff(c_6140, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6134, c_64])).
% 8.55/2.94  tff(c_6698, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6696, c_6140])).
% 8.55/2.94  tff(c_6702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4756, c_6698])).
% 8.55/2.94  tff(c_6704, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4510])).
% 8.55/2.94  tff(c_6703, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4510])).
% 8.55/2.94  tff(c_6812, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6704, c_6704, c_6703])).
% 8.55/2.94  tff(c_6813, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_6812])).
% 8.55/2.94  tff(c_6824, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6813, c_6813, c_4499])).
% 8.55/2.94  tff(c_6822, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6813, c_6704])).
% 8.55/2.94  tff(c_327, plain, (![C_78, B_4]: (v5_relat_1(C_78, B_4) | ~m1_subset_1(C_78, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_311])).
% 8.55/2.94  tff(c_7116, plain, (![C_717, B_718]: (v5_relat_1(C_717, B_718) | ~m1_subset_1(C_717, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6822, c_327])).
% 8.55/2.94  tff(c_7124, plain, (![B_718]: (v5_relat_1('#skF_1', B_718))), inference(resolution, [status(thm)], [c_6824, c_7116])).
% 8.55/2.94  tff(c_6711, plain, (![A_67]: (r1_tarski('#skF_3', A_67) | ~v5_relat_1('#skF_3', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_6704, c_6704, c_276])).
% 8.55/2.94  tff(c_7058, plain, (![A_67]: (r1_tarski('#skF_1', A_67) | ~v5_relat_1('#skF_1', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_6813, c_6813, c_6711])).
% 8.55/2.94  tff(c_7128, plain, (![A_67]: (r1_tarski('#skF_1', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_7124, c_7058])).
% 8.55/2.94  tff(c_4497, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4494, c_201])).
% 8.55/2.94  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/2.94  tff(c_4532, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4497, c_2])).
% 8.55/2.94  tff(c_4549, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_4532])).
% 8.55/2.94  tff(c_6823, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6813, c_4549])).
% 8.55/2.94  tff(c_7148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7128, c_6823])).
% 8.55/2.94  tff(c_7149, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_6812])).
% 8.55/2.94  tff(c_7150, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_6812])).
% 8.55/2.94  tff(c_7185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7149, c_7150])).
% 8.55/2.94  tff(c_7186, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4532])).
% 8.55/2.94  tff(c_7193, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7186, c_66])).
% 8.55/2.94  tff(c_9115, plain, (![C_948, D_949, B_950, A_951]: (k2_funct_1(C_948)=D_949 | k1_xboole_0=B_950 | k1_xboole_0=A_951 | ~v2_funct_1(C_948) | ~r2_relset_1(A_951, A_951, k1_partfun1(A_951, B_950, B_950, A_951, C_948, D_949), k6_partfun1(A_951)) | k2_relset_1(A_951, B_950, C_948)!=B_950 | ~m1_subset_1(D_949, k1_zfmisc_1(k2_zfmisc_1(B_950, A_951))) | ~v1_funct_2(D_949, B_950, A_951) | ~v1_funct_1(D_949) | ~m1_subset_1(C_948, k1_zfmisc_1(k2_zfmisc_1(A_951, B_950))) | ~v1_funct_2(C_948, A_951, B_950) | ~v1_funct_1(C_948))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.55/2.94  tff(c_9118, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_7193, c_9115])).
% 8.55/2.94  tff(c_9124, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4499, c_4494, c_8111, c_8202, c_9118])).
% 8.55/2.94  tff(c_9127, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_9124])).
% 8.55/2.94  tff(c_20, plain, (![B_11, A_10]: (v5_relat_1(B_11, A_10) | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.55/2.94  tff(c_7894, plain, (![A_10]: (v5_relat_1('#skF_3', A_10) | ~r1_tarski('#skF_1', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7883, c_20])).
% 8.55/2.94  tff(c_7905, plain, (![A_10]: (v5_relat_1('#skF_3', A_10) | ~r1_tarski('#skF_1', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_7894])).
% 8.55/2.94  tff(c_22, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.55/2.94  tff(c_278, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.55/2.94  tff(c_7378, plain, (![A_743, A_744, B_745]: (v4_relat_1(A_743, A_744) | ~r1_tarski(A_743, k2_zfmisc_1(A_744, B_745)))), inference(resolution, [status(thm)], [c_16, c_278])).
% 8.55/2.94  tff(c_8989, plain, (![B_935, A_936, B_937]: (v4_relat_1(k2_relat_1(B_935), A_936) | ~v5_relat_1(B_935, k2_zfmisc_1(A_936, B_937)) | ~v1_relat_1(B_935))), inference(resolution, [status(thm)], [c_22, c_7378])).
% 8.55/2.94  tff(c_9069, plain, (![B_946]: (v4_relat_1(k2_relat_1(B_946), k1_xboole_0) | ~v5_relat_1(B_946, k1_xboole_0) | ~v1_relat_1(B_946))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8989])).
% 8.55/2.94  tff(c_9072, plain, (v4_relat_1('#skF_1', k1_xboole_0) | ~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7883, c_9069])).
% 8.55/2.94  tff(c_9080, plain, (v4_relat_1('#skF_1', k1_xboole_0) | ~v5_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_219, c_9072])).
% 8.55/2.94  tff(c_9097, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_9080])).
% 8.55/2.94  tff(c_9104, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_7905, c_9097])).
% 8.55/2.94  tff(c_9129, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9127, c_9104])).
% 8.55/2.94  tff(c_9170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9129])).
% 8.55/2.94  tff(c_9171, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_9124])).
% 8.55/2.94  tff(c_8497, plain, (![A_879, B_880]: (k2_funct_2(A_879, B_880)=k2_funct_1(B_880) | ~m1_subset_1(B_880, k1_zfmisc_1(k2_zfmisc_1(A_879, A_879))) | ~v3_funct_2(B_880, A_879, A_879) | ~v1_funct_2(B_880, A_879, A_879) | ~v1_funct_1(B_880))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.55/2.94  tff(c_8941, plain, (![B_930]: (k2_funct_2('#skF_1', B_930)=k2_funct_1(B_930) | ~m1_subset_1(B_930, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_930, '#skF_1', '#skF_1') | ~v1_funct_2(B_930, '#skF_1', '#skF_1') | ~v1_funct_1(B_930))), inference(superposition, [status(thm), theory('equality')], [c_4494, c_8497])).
% 8.55/2.94  tff(c_8944, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4499, c_8941])).
% 8.55/2.94  tff(c_8951, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_8944])).
% 8.55/2.94  tff(c_7194, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7186, c_64])).
% 8.55/2.94  tff(c_8953, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8951, c_7194])).
% 8.55/2.94  tff(c_9173, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9171, c_8953])).
% 8.55/2.94  tff(c_9177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7990, c_9173])).
% 8.55/2.94  tff(c_9179, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_9080])).
% 8.55/2.94  tff(c_7220, plain, (![C_725, B_726]: (v5_relat_1(C_725, B_726) | ~m1_subset_1(C_725, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_311])).
% 8.55/2.94  tff(c_7264, plain, (![A_730, B_731]: (v5_relat_1(A_730, B_731) | ~r1_tarski(A_730, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_7220])).
% 8.55/2.94  tff(c_7268, plain, (![B_731]: (r1_tarski(k1_xboole_0, B_731) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_7264, c_276])).
% 8.55/2.94  tff(c_7273, plain, (![B_732]: (r1_tarski(k1_xboole_0, B_732))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7268])).
% 8.55/2.94  tff(c_7282, plain, (![B_733]: (k1_xboole_0=B_733 | ~r1_tarski(B_733, k1_xboole_0))), inference(resolution, [status(thm)], [c_7273, c_2])).
% 8.55/2.94  tff(c_7297, plain, (![B_11]: (k2_relat_1(B_11)=k1_xboole_0 | ~v5_relat_1(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_22, c_7282])).
% 8.55/2.94  tff(c_9184, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_9179, c_7297])).
% 8.55/2.94  tff(c_9196, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_219, c_7883, c_9184])).
% 8.55/2.94  tff(c_7219, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_4510])).
% 8.55/2.94  tff(c_9228, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9196, c_7219])).
% 8.55/2.94  tff(c_9238, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9196, c_9196, c_12])).
% 8.55/2.94  tff(c_9522, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9238, c_4494])).
% 8.55/2.94  tff(c_9524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9228, c_9522])).
% 8.55/2.94  tff(c_9526, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4510])).
% 8.55/2.94  tff(c_9525, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4510])).
% 8.55/2.94  tff(c_9659, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9526, c_9526, c_9525])).
% 8.55/2.94  tff(c_9660, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_9659])).
% 8.55/2.94  tff(c_9672, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9660, c_9660, c_4499])).
% 8.55/2.94  tff(c_9669, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9660, c_9526])).
% 8.55/2.94  tff(c_9930, plain, (![C_991, B_992]: (v5_relat_1(C_991, B_992) | ~m1_subset_1(C_991, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9669, c_327])).
% 8.55/2.94  tff(c_9936, plain, (![B_992]: (v5_relat_1('#skF_1', B_992))), inference(resolution, [status(thm)], [c_9672, c_9930])).
% 8.55/2.94  tff(c_9531, plain, (![A_67]: (r1_tarski('#skF_3', A_67) | ~v5_relat_1('#skF_3', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_9526, c_9526, c_276])).
% 8.55/2.94  tff(c_9871, plain, (![A_67]: (r1_tarski('#skF_1', A_67) | ~v5_relat_1('#skF_1', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_9660, c_9660, c_9531])).
% 8.55/2.94  tff(c_9940, plain, (![A_67]: (r1_tarski('#skF_1', A_67))), inference(demodulation, [status(thm), theory('equality')], [c_9936, c_9871])).
% 8.55/2.94  tff(c_9754, plain, (![A_973, B_974, D_975]: (r2_relset_1(A_973, B_974, D_975, D_975) | ~m1_subset_1(D_975, k1_zfmisc_1(k2_zfmisc_1(A_973, B_974))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.55/2.94  tff(c_10314, plain, (![A_1051, B_1052, A_1053]: (r2_relset_1(A_1051, B_1052, A_1053, A_1053) | ~r1_tarski(A_1053, k2_zfmisc_1(A_1051, B_1052)))), inference(resolution, [status(thm)], [c_16, c_9754])).
% 8.55/2.94  tff(c_10328, plain, (![A_1051, B_1052]: (r2_relset_1(A_1051, B_1052, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_9940, c_10314])).
% 8.55/2.94  tff(c_9677, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9660, c_72])).
% 8.55/2.94  tff(c_9678, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9660, c_70])).
% 8.55/2.94  tff(c_9679, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9660, c_74])).
% 8.55/2.94  tff(c_32, plain, (![A_15]: (k2_funct_1(k6_relat_1(A_15))=k6_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/2.94  tff(c_172, plain, (![A_53]: (k2_funct_1(k6_partfun1(A_53))=k6_partfun1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_32])).
% 8.55/2.94  tff(c_181, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_135, c_172])).
% 8.55/2.94  tff(c_184, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_181])).
% 8.55/2.94  tff(c_9533, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9526, c_9526, c_184])).
% 8.55/2.94  tff(c_9668, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9660, c_9660, c_9533])).
% 8.55/2.94  tff(c_10085, plain, (![A_1015, B_1016]: (k2_funct_2(A_1015, B_1016)=k2_funct_1(B_1016) | ~m1_subset_1(B_1016, k1_zfmisc_1(k2_zfmisc_1(A_1015, A_1015))) | ~v3_funct_2(B_1016, A_1015, A_1015) | ~v1_funct_2(B_1016, A_1015, A_1015) | ~v1_funct_1(B_1016))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.55/2.94  tff(c_11041, plain, (![A_1150, A_1151]: (k2_funct_2(A_1150, A_1151)=k2_funct_1(A_1151) | ~v3_funct_2(A_1151, A_1150, A_1150) | ~v1_funct_2(A_1151, A_1150, A_1150) | ~v1_funct_1(A_1151) | ~r1_tarski(A_1151, k2_zfmisc_1(A_1150, A_1150)))), inference(resolution, [status(thm)], [c_16, c_10085])).
% 8.55/2.94  tff(c_11045, plain, (![A_1150]: (k2_funct_2(A_1150, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_1150, A_1150) | ~v1_funct_2('#skF_1', A_1150, A_1150) | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_9940, c_11041])).
% 8.55/2.94  tff(c_11074, plain, (![A_1153]: (k2_funct_2(A_1153, '#skF_1')='#skF_1' | ~v3_funct_2('#skF_1', A_1153, A_1153) | ~v1_funct_2('#skF_1', A_1153, A_1153))), inference(demodulation, [status(thm), theory('equality')], [c_9679, c_9668, c_11045])).
% 8.55/2.94  tff(c_11077, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_9678, c_11074])).
% 8.55/2.94  tff(c_11080, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9677, c_11077])).
% 8.55/2.94  tff(c_9670, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9660, c_9660, c_7194])).
% 8.55/2.94  tff(c_11081, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11080, c_9670])).
% 8.55/2.94  tff(c_11084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10328, c_11081])).
% 8.55/2.94  tff(c_11085, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_9659])).
% 8.55/2.94  tff(c_11086, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_9659])).
% 8.55/2.94  tff(c_11113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11085, c_11086])).
% 8.55/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.55/2.94  
% 8.55/2.94  Inference rules
% 8.55/2.94  ----------------------
% 8.55/2.94  #Ref     : 0
% 8.55/2.94  #Sup     : 2188
% 8.55/2.94  #Fact    : 0
% 8.55/2.94  #Define  : 0
% 8.55/2.94  #Split   : 56
% 8.55/2.94  #Chain   : 0
% 8.55/2.94  #Close   : 0
% 8.55/2.94  
% 8.55/2.94  Ordering : KBO
% 8.55/2.94  
% 8.55/2.94  Simplification rules
% 8.55/2.94  ----------------------
% 8.55/2.94  #Subsume      : 298
% 8.55/2.94  #Demod        : 3112
% 8.55/2.94  #Tautology    : 1175
% 8.55/2.94  #SimpNegUnit  : 52
% 8.55/2.94  #BackRed      : 536
% 8.55/2.94  
% 8.55/2.94  #Partial instantiations: 0
% 8.55/2.94  #Strategies tried      : 1
% 8.55/2.94  
% 8.55/2.94  Timing (in seconds)
% 8.55/2.94  ----------------------
% 8.55/2.94  Preprocessing        : 0.37
% 8.55/2.94  Parsing              : 0.20
% 8.55/2.94  CNF conversion       : 0.03
% 8.55/2.94  Main loop            : 1.73
% 8.55/2.94  Inferencing          : 0.59
% 8.55/2.94  Reduction            : 0.62
% 8.55/2.94  Demodulation         : 0.44
% 8.55/2.94  BG Simplification    : 0.06
% 8.55/2.94  Subsumption          : 0.31
% 8.55/2.94  Abstraction          : 0.06
% 8.55/2.94  MUC search           : 0.00
% 8.55/2.94  Cooper               : 0.00
% 8.55/2.94  Total                : 2.20
% 8.55/2.94  Index Insertion      : 0.00
% 8.55/2.94  Index Deletion       : 0.00
% 8.55/2.94  Index Matching       : 0.00
% 8.55/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
