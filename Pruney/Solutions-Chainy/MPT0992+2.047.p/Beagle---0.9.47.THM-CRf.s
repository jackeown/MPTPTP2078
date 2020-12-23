%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:38 EST 2020

% Result     : Theorem 37.01s
% Output     : CNFRefutation 37.01s
% Verified   : 
% Statistics : Number of formulae       :  242 (4291 expanded)
%              Number of leaves         :   42 (1317 expanded)
%              Depth                    :   15
%              Number of atoms          :  404 (12326 expanded)
%              Number of equality atoms :  131 (5464 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(c_76,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_152630,plain,(
    ! [C_2106,A_2107,B_2108] :
      ( v1_relat_1(C_2106)
      | ~ m1_subset_1(C_2106,k1_zfmisc_1(k2_zfmisc_1(A_2107,B_2108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_152647,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_152630])).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_97,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_153105,plain,(
    ! [A_2181,B_2182,C_2183] :
      ( k1_relset_1(A_2181,B_2182,C_2183) = k1_relat_1(C_2183)
      | ~ m1_subset_1(C_2183,k1_zfmisc_1(k2_zfmisc_1(A_2181,B_2182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_153128,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_153105])).

tff(c_153799,plain,(
    ! [B_2253,A_2254,C_2255] :
      ( k1_xboole_0 = B_2253
      | k1_relset_1(A_2254,B_2253,C_2255) = A_2254
      | ~ v1_funct_2(C_2255,A_2254,B_2253)
      | ~ m1_subset_1(C_2255,k1_zfmisc_1(k2_zfmisc_1(A_2254,B_2253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_153809,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_153799])).

tff(c_153824,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_153128,c_153809])).

tff(c_153825,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_153824])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_153839,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153825,c_32])).

tff(c_153850,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152647,c_153839])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_153739,plain,(
    ! [A_2247,B_2248,C_2249,D_2250] :
      ( k2_partfun1(A_2247,B_2248,C_2249,D_2250) = k7_relat_1(C_2249,D_2250)
      | ~ m1_subset_1(C_2249,k1_zfmisc_1(k2_zfmisc_1(A_2247,B_2248)))
      | ~ v1_funct_1(C_2249) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_153748,plain,(
    ! [D_2250] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_2250) = k7_relat_1('#skF_4',D_2250)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_153739])).

tff(c_153763,plain,(
    ! [D_2250] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_2250) = k7_relat_1('#skF_4',D_2250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_153748])).

tff(c_1144,plain,(
    ! [C_190,A_191,B_192] :
      ( v1_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1161,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1144])).

tff(c_1290,plain,(
    ! [C_218,B_219,A_220] :
      ( v5_relat_1(C_218,B_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1309,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1290])).

tff(c_38,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_relat_1(k7_relat_1(C_22,A_20))
      | ~ v5_relat_1(C_22,B_21)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1313,plain,(
    ! [A_20] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_20))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1309,c_38])).

tff(c_1316,plain,(
    ! [A_20] : v1_relat_1(k7_relat_1('#skF_4',A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_1313])).

tff(c_3818,plain,(
    ! [A_454,B_455,C_456,D_457] :
      ( k2_partfun1(A_454,B_455,C_456,D_457) = k7_relat_1(C_456,D_457)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(A_454,B_455)))
      | ~ v1_funct_1(C_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3825,plain,(
    ! [D_457] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_457) = k7_relat_1('#skF_4',D_457)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_3818])).

tff(c_3837,plain,(
    ! [D_457] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_457) = k7_relat_1('#skF_4',D_457) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3825])).

tff(c_4162,plain,(
    ! [A_481,B_482,C_483,D_484] :
      ( m1_subset_1(k2_partfun1(A_481,B_482,C_483,D_484),k1_zfmisc_1(k2_zfmisc_1(A_481,B_482)))
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1(A_481,B_482)))
      | ~ v1_funct_1(C_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4192,plain,(
    ! [D_457] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_457),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3837,c_4162])).

tff(c_4218,plain,(
    ! [D_485] : m1_subset_1(k7_relat_1('#skF_4',D_485),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_4192])).

tff(c_42,plain,(
    ! [C_28,B_27,A_26] :
      ( v5_relat_1(C_28,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4266,plain,(
    ! [D_485] : v5_relat_1(k7_relat_1('#skF_4',D_485),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4218,c_42])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3657,plain,(
    ! [A_420,B_421,C_422,D_423] :
      ( v1_funct_1(k2_partfun1(A_420,B_421,C_422,D_423))
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421)))
      | ~ v1_funct_1(C_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3662,plain,(
    ! [D_423] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_423))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_3657])).

tff(c_3673,plain,(
    ! [D_423] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_423)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3662])).

tff(c_3862,plain,(
    ! [D_423] : v1_funct_1(k7_relat_1('#skF_4',D_423)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3837,c_3673])).

tff(c_1470,plain,(
    ! [A_252,B_253,C_254] :
      ( k1_relset_1(A_252,B_253,C_254) = k1_relat_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1489,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1470])).

tff(c_4047,plain,(
    ! [B_475,A_476,C_477] :
      ( k1_xboole_0 = B_475
      | k1_relset_1(A_476,B_475,C_477) = A_476
      | ~ v1_funct_2(C_477,A_476,B_475)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k2_zfmisc_1(A_476,B_475))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4057,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_4047])).

tff(c_4072,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1489,c_4057])).

tff(c_4073,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_4072])).

tff(c_4087,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4073,c_32])).

tff(c_4362,plain,(
    ! [A_492] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_492)) = A_492
      | ~ r1_tarski(A_492,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_4087])).

tff(c_66,plain,(
    ! [B_44,A_43] :
      ( m1_subset_1(B_44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44),A_43)))
      | ~ r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4368,plain,(
    ! [A_492,A_43] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_492),k1_zfmisc_1(k2_zfmisc_1(A_492,A_43)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_492)),A_43)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_492))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_492))
      | ~ r1_tarski(A_492,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4362,c_66])).

tff(c_152422,plain,(
    ! [A_2102,A_2103] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_2102),k1_zfmisc_1(k2_zfmisc_1(A_2102,A_2103)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_2102)),A_2103)
      | ~ r1_tarski(A_2102,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_3862,c_4368])).

tff(c_1057,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( v1_funct_1(k2_partfun1(A_178,B_179,C_180,D_181))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1062,plain,(
    ! [D_181] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_181))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_1057])).

tff(c_1073,plain,(
    ! [D_181] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_181)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1062])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_147,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_1077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_147])).

tff(c_1078,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1132,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1078])).

tff(c_3864,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3837,c_1132])).

tff(c_152449,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_152422,c_3864])).

tff(c_152561,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_152449])).

tff(c_152608,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_152561])).

tff(c_152616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_4266,c_152608])).

tff(c_152618,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1078])).

tff(c_153126,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_152618,c_153105])).

tff(c_153768,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153763,c_153763,c_153126])).

tff(c_152617,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1078])).

tff(c_153776,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153763,c_152617])).

tff(c_153775,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153763,c_152618])).

tff(c_153959,plain,(
    ! [B_2258,C_2259,A_2260] :
      ( k1_xboole_0 = B_2258
      | v1_funct_2(C_2259,A_2260,B_2258)
      | k1_relset_1(A_2260,B_2258,C_2259) != A_2260
      | ~ m1_subset_1(C_2259,k1_zfmisc_1(k2_zfmisc_1(A_2260,B_2258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_153962,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_153775,c_153959])).

tff(c_153985,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_153776,c_97,c_153962])).

tff(c_154316,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153768,c_153985])).

tff(c_154323,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_153850,c_154316])).

tff(c_154327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_154323])).

tff(c_154328,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154355,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154328,c_154328,c_10])).

tff(c_154329,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_154338,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154328,c_154329])).

tff(c_154391,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154355,c_154338,c_78])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154363,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154328,c_154328,c_12])).

tff(c_157963,plain,(
    ! [C_2649,A_2650,B_2651] :
      ( v1_relat_1(C_2649)
      | ~ m1_subset_1(C_2649,k1_zfmisc_1(k2_zfmisc_1(A_2650,B_2651))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_157979,plain,(
    ! [C_2652] :
      ( v1_relat_1(C_2652)
      | ~ m1_subset_1(C_2652,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154363,c_157963])).

tff(c_157992,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_154391,c_157979])).

tff(c_156333,plain,(
    ! [A_2476,B_2477] :
      ( r1_tarski(A_2476,B_2477)
      | ~ m1_subset_1(A_2476,k1_zfmisc_1(B_2477)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_156344,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_154391,c_156333])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_154331,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154328,c_154328,c_30])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154353,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154328,c_14])).

tff(c_156360,plain,(
    ! [C_2479,A_2480,B_2481] :
      ( v1_relat_1(C_2479)
      | ~ m1_subset_1(C_2479,k1_zfmisc_1(k2_zfmisc_1(A_2480,B_2481))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_156374,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_154353,c_156360])).

tff(c_156347,plain,(
    ! [A_2478] :
      ( k7_relat_1(A_2478,k1_relat_1(A_2478)) = A_2478
      | ~ v1_relat_1(A_2478) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_156356,plain,
    ( k7_relat_1('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_154331,c_156347])).

tff(c_156359,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_156356])).

tff(c_156376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156374,c_156359])).

tff(c_156378,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_156356])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_154332,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154328,c_4])).

tff(c_156377,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_156356])).

tff(c_158486,plain,(
    ! [C_2733,A_2734,B_2735] :
      ( k7_relat_1(k7_relat_1(C_2733,A_2734),B_2735) = k7_relat_1(C_2733,A_2734)
      | ~ r1_tarski(A_2734,B_2735)
      | ~ v1_relat_1(C_2733) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_158515,plain,(
    ! [B_2735] :
      ( k7_relat_1('#skF_1',B_2735) = k7_relat_1('#skF_1','#skF_1')
      | ~ r1_tarski('#skF_1',B_2735)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156377,c_158486])).

tff(c_158527,plain,(
    ! [B_2735] : k7_relat_1('#skF_1',B_2735) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156378,c_154332,c_156377,c_158515])).

tff(c_158293,plain,(
    ! [B_2713,A_2714] :
      ( k1_relat_1(k7_relat_1(B_2713,A_2714)) = A_2714
      | ~ r1_tarski(A_2714,k1_relat_1(B_2713))
      | ~ v1_relat_1(B_2713) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_158304,plain,(
    ! [A_2714] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_2714)) = A_2714
      | ~ r1_tarski(A_2714,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154331,c_158293])).

tff(c_158308,plain,(
    ! [A_2714] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_2714)) = A_2714
      | ~ r1_tarski(A_2714,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156378,c_158304])).

tff(c_158529,plain,(
    ! [A_2714] :
      ( k1_relat_1('#skF_1') = A_2714
      | ~ r1_tarski(A_2714,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158527,c_158308])).

tff(c_158576,plain,(
    ! [A_2737] :
      ( A_2737 = '#skF_1'
      | ~ r1_tarski(A_2737,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154331,c_158529])).

tff(c_158596,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_156344,c_158576])).

tff(c_158638,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158596,c_154332])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_154330,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154328,c_154328,c_28])).

tff(c_158641,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158596,c_158596,c_154330])).

tff(c_158639,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158596,c_158596,c_154331])).

tff(c_158762,plain,(
    ! [B_2742,A_2743] :
      ( v1_funct_2(B_2742,k1_relat_1(B_2742),A_2743)
      | ~ r1_tarski(k2_relat_1(B_2742),A_2743)
      | ~ v1_funct_1(B_2742)
      | ~ v1_relat_1(B_2742) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_158765,plain,(
    ! [A_2743] :
      ( v1_funct_2('#skF_4','#skF_4',A_2743)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_2743)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158639,c_158762])).

tff(c_158767,plain,(
    ! [A_2743] : v1_funct_2('#skF_4','#skF_4',A_2743) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157992,c_82,c_158638,c_158641,c_158765])).

tff(c_158599,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_76,c_158576])).

tff(c_158653,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158596,c_158599])).

tff(c_157275,plain,(
    ! [C_2595,A_2596,B_2597] :
      ( k7_relat_1(k7_relat_1(C_2595,A_2596),B_2597) = k7_relat_1(C_2595,A_2596)
      | ~ r1_tarski(A_2596,B_2597)
      | ~ v1_relat_1(C_2595) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157304,plain,(
    ! [B_2597] :
      ( k7_relat_1('#skF_1',B_2597) = k7_relat_1('#skF_1','#skF_1')
      | ~ r1_tarski('#skF_1',B_2597)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156377,c_157275])).

tff(c_157316,plain,(
    ! [B_2597] : k7_relat_1('#skF_1',B_2597) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156378,c_154332,c_156377,c_157304])).

tff(c_156676,plain,(
    ! [B_2542,A_2543] :
      ( k1_relat_1(k7_relat_1(B_2542,A_2543)) = A_2543
      | ~ r1_tarski(A_2543,k1_relat_1(B_2542))
      | ~ v1_relat_1(B_2542) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_156687,plain,(
    ! [A_2543] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_2543)) = A_2543
      | ~ r1_tarski(A_2543,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154331,c_156676])).

tff(c_156691,plain,(
    ! [A_2543] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_2543)) = A_2543
      | ~ r1_tarski(A_2543,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156378,c_156687])).

tff(c_157318,plain,(
    ! [A_2543] :
      ( k1_relat_1('#skF_1') = A_2543
      | ~ r1_tarski(A_2543,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157316,c_156691])).

tff(c_157365,plain,(
    ! [A_2599] :
      ( A_2599 = '#skF_1'
      | ~ r1_tarski(A_2599,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154331,c_157318])).

tff(c_157381,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_156344,c_157365])).

tff(c_157425,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157381,c_154332])).

tff(c_157386,plain,(
    ! [B_2597] : k7_relat_1('#skF_4',B_2597) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157381,c_157381,c_157316])).

tff(c_157424,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157381,c_154353])).

tff(c_157847,plain,(
    ! [A_2631,B_2632,C_2633,D_2634] :
      ( k2_partfun1(A_2631,B_2632,C_2633,D_2634) = k7_relat_1(C_2633,D_2634)
      | ~ m1_subset_1(C_2633,k1_zfmisc_1(k2_zfmisc_1(A_2631,B_2632)))
      | ~ v1_funct_1(C_2633) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_157854,plain,(
    ! [A_2631,B_2632,D_2634] :
      ( k2_partfun1(A_2631,B_2632,'#skF_4',D_2634) = k7_relat_1('#skF_4',D_2634)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_157424,c_157847])).

tff(c_157863,plain,(
    ! [A_2631,B_2632,D_2634] : k2_partfun1(A_2631,B_2632,'#skF_4',D_2634) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_157386,c_157854])).

tff(c_157384,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_76,c_157365])).

tff(c_157441,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157381,c_157384])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_154485,plain,(
    ! [C_2307,A_2308,B_2309] :
      ( v1_relat_1(C_2307)
      | ~ m1_subset_1(C_2307,k1_zfmisc_1(k2_zfmisc_1(A_2308,B_2309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_154501,plain,(
    ! [C_2310] :
      ( v1_relat_1(C_2310)
      | ~ m1_subset_1(C_2310,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154363,c_154485])).

tff(c_154514,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_154391,c_154501])).

tff(c_154870,plain,(
    ! [A_2372,B_2373,C_2374] :
      ( k1_relset_1(A_2372,B_2373,C_2374) = k1_relat_1(C_2374)
      | ~ m1_subset_1(C_2374,k1_zfmisc_1(k2_zfmisc_1(A_2372,B_2373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_154901,plain,(
    ! [B_2378,C_2379] :
      ( k1_relset_1('#skF_1',B_2378,C_2379) = k1_relat_1(C_2379)
      | ~ m1_subset_1(C_2379,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154363,c_154870])).

tff(c_154911,plain,(
    ! [B_2378] : k1_relset_1('#skF_1',B_2378,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_154391,c_154901])).

tff(c_154347,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154338,c_80])).

tff(c_56,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_85,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_56])).

tff(c_155127,plain,(
    ! [B_2402,C_2403] :
      ( k1_relset_1('#skF_1',B_2402,C_2403) = '#skF_1'
      | ~ v1_funct_2(C_2403,'#skF_1',B_2402)
      | ~ m1_subset_1(C_2403,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154328,c_154328,c_154328,c_154328,c_85])).

tff(c_155132,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_154347,c_155127])).

tff(c_155139,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154391,c_154911,c_155132])).

tff(c_34,plain,(
    ! [A_19] :
      ( k7_relat_1(A_19,k1_relat_1(A_19)) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_155148,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_155139,c_34])).

tff(c_155154,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154514,c_155148])).

tff(c_155597,plain,(
    ! [C_2431,A_2432,B_2433] :
      ( k7_relat_1(k7_relat_1(C_2431,A_2432),B_2433) = k7_relat_1(C_2431,A_2432)
      | ~ r1_tarski(A_2432,B_2433)
      | ~ v1_relat_1(C_2431) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_155650,plain,(
    ! [B_2433] :
      ( k7_relat_1('#skF_4',B_2433) = k7_relat_1('#skF_4','#skF_1')
      | ~ r1_tarski('#skF_1',B_2433)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155154,c_155597])).

tff(c_155683,plain,(
    ! [B_2433] : k7_relat_1('#skF_4',B_2433) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154514,c_154332,c_155154,c_155650])).

tff(c_154454,plain,(
    ! [A_2301,B_2302] :
      ( r1_tarski(A_2301,B_2302)
      | ~ m1_subset_1(A_2301,k1_zfmisc_1(B_2302)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_154461,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_154391,c_154454])).

tff(c_154394,plain,(
    ! [A_2291] :
      ( k7_relat_1(A_2291,k1_relat_1(A_2291)) = A_2291
      | ~ v1_relat_1(A_2291) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_154403,plain,
    ( k7_relat_1('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_154331,c_154394])).

tff(c_154406,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_154403])).

tff(c_154434,plain,(
    ! [C_2298,A_2299,B_2300] :
      ( v1_relat_1(C_2298)
      | ~ m1_subset_1(C_2298,k1_zfmisc_1(k2_zfmisc_1(A_2299,B_2300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_154446,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_154353,c_154434])).

tff(c_154451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154406,c_154446])).

tff(c_154453,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_154403])).

tff(c_154452,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_154403])).

tff(c_155653,plain,(
    ! [B_2433] :
      ( k7_relat_1('#skF_1',B_2433) = k7_relat_1('#skF_1','#skF_1')
      | ~ r1_tarski('#skF_1',B_2433)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154452,c_155597])).

tff(c_155685,plain,(
    ! [B_2433] : k7_relat_1('#skF_1',B_2433) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154453,c_154332,c_154452,c_155653])).

tff(c_154752,plain,(
    ! [B_2363,A_2364] :
      ( k1_relat_1(k7_relat_1(B_2363,A_2364)) = A_2364
      | ~ r1_tarski(A_2364,k1_relat_1(B_2363))
      | ~ v1_relat_1(B_2363) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_154763,plain,(
    ! [A_2364] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_2364)) = A_2364
      | ~ r1_tarski(A_2364,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154331,c_154752])).

tff(c_154767,plain,(
    ! [A_2364] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_2364)) = A_2364
      | ~ r1_tarski(A_2364,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154453,c_154763])).

tff(c_155688,plain,(
    ! [A_2364] :
      ( k1_relat_1('#skF_1') = A_2364
      | ~ r1_tarski(A_2364,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155685,c_154767])).

tff(c_155785,plain,(
    ! [A_2436] :
      ( A_2436 = '#skF_1'
      | ~ r1_tarski(A_2436,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154331,c_155688])).

tff(c_155801,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_154461,c_155785])).

tff(c_155858,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155801,c_154353])).

tff(c_156191,plain,(
    ! [A_2452,B_2453,C_2454,D_2455] :
      ( k2_partfun1(A_2452,B_2453,C_2454,D_2455) = k7_relat_1(C_2454,D_2455)
      | ~ m1_subset_1(C_2454,k1_zfmisc_1(k2_zfmisc_1(A_2452,B_2453)))
      | ~ v1_funct_1(C_2454) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_156196,plain,(
    ! [A_2452,B_2453,D_2455] :
      ( k2_partfun1(A_2452,B_2453,'#skF_4',D_2455) = k7_relat_1('#skF_4',D_2455)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_155858,c_156191])).

tff(c_156206,plain,(
    ! [A_2452,B_2453,D_2455] : k2_partfun1(A_2452,B_2453,'#skF_4',D_2455) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_155683,c_156196])).

tff(c_155804,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_76,c_155785])).

tff(c_154392,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154338,c_154338,c_154338,c_154355,c_154338,c_154338,c_72])).

tff(c_154393,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_154392])).

tff(c_155808,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155804,c_154393])).

tff(c_156245,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155801,c_155801,c_155801,c_155808])).

tff(c_156326,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156206,c_156245])).

tff(c_156329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_156326])).

tff(c_156330,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_154392])).

tff(c_156379,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_156330])).

tff(c_156458,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_156379])).

tff(c_157411,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157381,c_157381,c_157381,c_156458])).

tff(c_157956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157425,c_157863,c_157441,c_157411])).

tff(c_157958,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_156330])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_158041,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_157958,c_16])).

tff(c_158595,plain,(
    k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_158041,c_158576])).

tff(c_158933,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158653,c_158596,c_158596,c_158596,c_158595])).

tff(c_157957,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_156330])).

tff(c_158628,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158596,c_158596,c_158596,c_157957])).

tff(c_159091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158767,c_158933,c_158653,c_158653,c_158628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.01/25.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.01/26.02  
% 37.01/26.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.01/26.02  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 37.01/26.02  
% 37.01/26.02  %Foreground sorts:
% 37.01/26.02  
% 37.01/26.02  
% 37.01/26.02  %Background operators:
% 37.01/26.02  
% 37.01/26.02  
% 37.01/26.02  %Foreground operators:
% 37.01/26.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 37.01/26.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.01/26.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.01/26.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 37.01/26.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.01/26.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 37.01/26.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 37.01/26.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 37.01/26.02  tff('#skF_2', type, '#skF_2': $i).
% 37.01/26.02  tff('#skF_3', type, '#skF_3': $i).
% 37.01/26.02  tff('#skF_1', type, '#skF_1': $i).
% 37.01/26.02  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 37.01/26.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 37.01/26.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 37.01/26.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.01/26.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 37.01/26.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 37.01/26.02  tff('#skF_4', type, '#skF_4': $i).
% 37.01/26.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.01/26.02  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 37.01/26.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 37.01/26.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 37.01/26.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 37.01/26.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 37.01/26.02  
% 37.01/26.05  tff(f_165, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 37.01/26.05  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 37.01/26.05  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 37.01/26.05  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 37.01/26.05  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 37.01/26.05  tff(f_133, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 37.01/26.05  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 37.01/26.05  tff(f_87, axiom, (![A, B, C]: ((v1_relat_1(C) & v5_relat_1(C, B)) => (v1_relat_1(k7_relat_1(C, A)) & v5_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc22_relat_1)).
% 37.01/26.05  tff(f_127, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 37.01/26.05  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 37.01/26.05  tff(f_145, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 37.01/26.05  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 37.01/26.05  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 37.01/26.05  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 37.01/26.05  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 37.01/26.05  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 37.01/26.05  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 37.01/26.05  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 37.01/26.05  tff(c_76, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 37.01/26.05  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 37.01/26.05  tff(c_152630, plain, (![C_2106, A_2107, B_2108]: (v1_relat_1(C_2106) | ~m1_subset_1(C_2106, k1_zfmisc_1(k2_zfmisc_1(A_2107, B_2108))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 37.01/26.05  tff(c_152647, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_152630])).
% 37.01/26.05  tff(c_74, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 37.01/26.05  tff(c_97, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_74])).
% 37.01/26.05  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 37.01/26.05  tff(c_153105, plain, (![A_2181, B_2182, C_2183]: (k1_relset_1(A_2181, B_2182, C_2183)=k1_relat_1(C_2183) | ~m1_subset_1(C_2183, k1_zfmisc_1(k2_zfmisc_1(A_2181, B_2182))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 37.01/26.05  tff(c_153128, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_153105])).
% 37.01/26.05  tff(c_153799, plain, (![B_2253, A_2254, C_2255]: (k1_xboole_0=B_2253 | k1_relset_1(A_2254, B_2253, C_2255)=A_2254 | ~v1_funct_2(C_2255, A_2254, B_2253) | ~m1_subset_1(C_2255, k1_zfmisc_1(k2_zfmisc_1(A_2254, B_2253))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 37.01/26.05  tff(c_153809, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_153799])).
% 37.01/26.05  tff(c_153824, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_153128, c_153809])).
% 37.01/26.05  tff(c_153825, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_97, c_153824])).
% 37.01/26.05  tff(c_32, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 37.01/26.05  tff(c_153839, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_153825, c_32])).
% 37.01/26.05  tff(c_153850, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_152647, c_153839])).
% 37.01/26.05  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 37.01/26.05  tff(c_153739, plain, (![A_2247, B_2248, C_2249, D_2250]: (k2_partfun1(A_2247, B_2248, C_2249, D_2250)=k7_relat_1(C_2249, D_2250) | ~m1_subset_1(C_2249, k1_zfmisc_1(k2_zfmisc_1(A_2247, B_2248))) | ~v1_funct_1(C_2249))), inference(cnfTransformation, [status(thm)], [f_133])).
% 37.01/26.05  tff(c_153748, plain, (![D_2250]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2250)=k7_relat_1('#skF_4', D_2250) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_153739])).
% 37.01/26.05  tff(c_153763, plain, (![D_2250]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2250)=k7_relat_1('#skF_4', D_2250))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_153748])).
% 37.01/26.05  tff(c_1144, plain, (![C_190, A_191, B_192]: (v1_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 37.01/26.05  tff(c_1161, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1144])).
% 37.01/26.05  tff(c_1290, plain, (![C_218, B_219, A_220]: (v5_relat_1(C_218, B_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 37.01/26.05  tff(c_1309, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_1290])).
% 37.01/26.05  tff(c_38, plain, (![C_22, A_20, B_21]: (v1_relat_1(k7_relat_1(C_22, A_20)) | ~v5_relat_1(C_22, B_21) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 37.01/26.05  tff(c_1313, plain, (![A_20]: (v1_relat_1(k7_relat_1('#skF_4', A_20)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1309, c_38])).
% 37.01/26.05  tff(c_1316, plain, (![A_20]: (v1_relat_1(k7_relat_1('#skF_4', A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_1161, c_1313])).
% 37.01/26.05  tff(c_3818, plain, (![A_454, B_455, C_456, D_457]: (k2_partfun1(A_454, B_455, C_456, D_457)=k7_relat_1(C_456, D_457) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(A_454, B_455))) | ~v1_funct_1(C_456))), inference(cnfTransformation, [status(thm)], [f_133])).
% 37.01/26.05  tff(c_3825, plain, (![D_457]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_457)=k7_relat_1('#skF_4', D_457) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_3818])).
% 37.01/26.05  tff(c_3837, plain, (![D_457]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_457)=k7_relat_1('#skF_4', D_457))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3825])).
% 37.01/26.05  tff(c_4162, plain, (![A_481, B_482, C_483, D_484]: (m1_subset_1(k2_partfun1(A_481, B_482, C_483, D_484), k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_zfmisc_1(A_481, B_482))) | ~v1_funct_1(C_483))), inference(cnfTransformation, [status(thm)], [f_127])).
% 37.01/26.05  tff(c_4192, plain, (![D_457]: (m1_subset_1(k7_relat_1('#skF_4', D_457), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3837, c_4162])).
% 37.01/26.05  tff(c_4218, plain, (![D_485]: (m1_subset_1(k7_relat_1('#skF_4', D_485), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_4192])).
% 37.01/26.05  tff(c_42, plain, (![C_28, B_27, A_26]: (v5_relat_1(C_28, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 37.01/26.05  tff(c_4266, plain, (![D_485]: (v5_relat_1(k7_relat_1('#skF_4', D_485), '#skF_2'))), inference(resolution, [status(thm)], [c_4218, c_42])).
% 37.01/26.05  tff(c_24, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 37.01/26.05  tff(c_3657, plain, (![A_420, B_421, C_422, D_423]: (v1_funct_1(k2_partfun1(A_420, B_421, C_422, D_423)) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))) | ~v1_funct_1(C_422))), inference(cnfTransformation, [status(thm)], [f_127])).
% 37.01/26.05  tff(c_3662, plain, (![D_423]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_423)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_3657])).
% 37.01/26.05  tff(c_3673, plain, (![D_423]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_423)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3662])).
% 37.01/26.05  tff(c_3862, plain, (![D_423]: (v1_funct_1(k7_relat_1('#skF_4', D_423)))), inference(demodulation, [status(thm), theory('equality')], [c_3837, c_3673])).
% 37.01/26.05  tff(c_1470, plain, (![A_252, B_253, C_254]: (k1_relset_1(A_252, B_253, C_254)=k1_relat_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 37.01/26.05  tff(c_1489, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1470])).
% 37.01/26.05  tff(c_4047, plain, (![B_475, A_476, C_477]: (k1_xboole_0=B_475 | k1_relset_1(A_476, B_475, C_477)=A_476 | ~v1_funct_2(C_477, A_476, B_475) | ~m1_subset_1(C_477, k1_zfmisc_1(k2_zfmisc_1(A_476, B_475))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 37.01/26.05  tff(c_4057, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_4047])).
% 37.01/26.05  tff(c_4072, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1489, c_4057])).
% 37.01/26.05  tff(c_4073, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_97, c_4072])).
% 37.01/26.05  tff(c_4087, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4073, c_32])).
% 37.01/26.05  tff(c_4362, plain, (![A_492]: (k1_relat_1(k7_relat_1('#skF_4', A_492))=A_492 | ~r1_tarski(A_492, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1161, c_4087])).
% 37.01/26.05  tff(c_66, plain, (![B_44, A_43]: (m1_subset_1(B_44, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44), A_43))) | ~r1_tarski(k2_relat_1(B_44), A_43) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_145])).
% 37.01/26.05  tff(c_4368, plain, (![A_492, A_43]: (m1_subset_1(k7_relat_1('#skF_4', A_492), k1_zfmisc_1(k2_zfmisc_1(A_492, A_43))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_492)), A_43) | ~v1_funct_1(k7_relat_1('#skF_4', A_492)) | ~v1_relat_1(k7_relat_1('#skF_4', A_492)) | ~r1_tarski(A_492, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4362, c_66])).
% 37.01/26.05  tff(c_152422, plain, (![A_2102, A_2103]: (m1_subset_1(k7_relat_1('#skF_4', A_2102), k1_zfmisc_1(k2_zfmisc_1(A_2102, A_2103))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_2102)), A_2103) | ~r1_tarski(A_2102, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1316, c_3862, c_4368])).
% 37.01/26.05  tff(c_1057, plain, (![A_178, B_179, C_180, D_181]: (v1_funct_1(k2_partfun1(A_178, B_179, C_180, D_181)) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_1(C_180))), inference(cnfTransformation, [status(thm)], [f_127])).
% 37.01/26.05  tff(c_1062, plain, (![D_181]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_181)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_1057])).
% 37.01/26.05  tff(c_1073, plain, (![D_181]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_181)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1062])).
% 37.01/26.05  tff(c_72, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 37.01/26.05  tff(c_147, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 37.01/26.05  tff(c_1077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1073, c_147])).
% 37.01/26.05  tff(c_1078, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_72])).
% 37.01/26.05  tff(c_1132, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1078])).
% 37.01/26.05  tff(c_3864, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3837, c_1132])).
% 37.01/26.05  tff(c_152449, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_152422, c_3864])).
% 37.01/26.05  tff(c_152561, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_152449])).
% 37.01/26.05  tff(c_152608, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_152561])).
% 37.01/26.05  tff(c_152616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1316, c_4266, c_152608])).
% 37.01/26.05  tff(c_152618, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1078])).
% 37.01/26.05  tff(c_153126, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_152618, c_153105])).
% 37.01/26.05  tff(c_153768, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_153763, c_153763, c_153126])).
% 37.01/26.06  tff(c_152617, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1078])).
% 37.01/26.06  tff(c_153776, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_153763, c_152617])).
% 37.01/26.06  tff(c_153775, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_153763, c_152618])).
% 37.01/26.06  tff(c_153959, plain, (![B_2258, C_2259, A_2260]: (k1_xboole_0=B_2258 | v1_funct_2(C_2259, A_2260, B_2258) | k1_relset_1(A_2260, B_2258, C_2259)!=A_2260 | ~m1_subset_1(C_2259, k1_zfmisc_1(k2_zfmisc_1(A_2260, B_2258))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 37.01/26.06  tff(c_153962, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_153775, c_153959])).
% 37.01/26.06  tff(c_153985, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_153776, c_97, c_153962])).
% 37.01/26.06  tff(c_154316, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_153768, c_153985])).
% 37.01/26.06  tff(c_154323, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_153850, c_154316])).
% 37.01/26.06  tff(c_154327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_154323])).
% 37.01/26.06  tff(c_154328, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_74])).
% 37.01/26.06  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 37.01/26.06  tff(c_154355, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154328, c_154328, c_10])).
% 37.01/26.06  tff(c_154329, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_74])).
% 37.01/26.06  tff(c_154338, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154328, c_154329])).
% 37.01/26.06  tff(c_154391, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154355, c_154338, c_78])).
% 37.01/26.06  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 37.01/26.06  tff(c_154363, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154328, c_154328, c_12])).
% 37.01/26.06  tff(c_157963, plain, (![C_2649, A_2650, B_2651]: (v1_relat_1(C_2649) | ~m1_subset_1(C_2649, k1_zfmisc_1(k2_zfmisc_1(A_2650, B_2651))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 37.01/26.06  tff(c_157979, plain, (![C_2652]: (v1_relat_1(C_2652) | ~m1_subset_1(C_2652, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_154363, c_157963])).
% 37.01/26.06  tff(c_157992, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_154391, c_157979])).
% 37.01/26.06  tff(c_156333, plain, (![A_2476, B_2477]: (r1_tarski(A_2476, B_2477) | ~m1_subset_1(A_2476, k1_zfmisc_1(B_2477)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 37.01/26.06  tff(c_156344, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_154391, c_156333])).
% 37.01/26.06  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 37.01/26.06  tff(c_154331, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154328, c_154328, c_30])).
% 37.01/26.06  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.01/26.06  tff(c_154353, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_154328, c_14])).
% 37.01/26.06  tff(c_156360, plain, (![C_2479, A_2480, B_2481]: (v1_relat_1(C_2479) | ~m1_subset_1(C_2479, k1_zfmisc_1(k2_zfmisc_1(A_2480, B_2481))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 37.01/26.06  tff(c_156374, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_154353, c_156360])).
% 37.01/26.06  tff(c_156347, plain, (![A_2478]: (k7_relat_1(A_2478, k1_relat_1(A_2478))=A_2478 | ~v1_relat_1(A_2478))), inference(cnfTransformation, [status(thm)], [f_79])).
% 37.01/26.06  tff(c_156356, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_154331, c_156347])).
% 37.01/26.06  tff(c_156359, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_156356])).
% 37.01/26.06  tff(c_156376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156374, c_156359])).
% 37.01/26.06  tff(c_156378, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_156356])).
% 37.01/26.06  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 37.01/26.06  tff(c_154332, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_154328, c_4])).
% 37.01/26.06  tff(c_156377, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_156356])).
% 37.01/26.06  tff(c_158486, plain, (![C_2733, A_2734, B_2735]: (k7_relat_1(k7_relat_1(C_2733, A_2734), B_2735)=k7_relat_1(C_2733, A_2734) | ~r1_tarski(A_2734, B_2735) | ~v1_relat_1(C_2733))), inference(cnfTransformation, [status(thm)], [f_66])).
% 37.01/26.06  tff(c_158515, plain, (![B_2735]: (k7_relat_1('#skF_1', B_2735)=k7_relat_1('#skF_1', '#skF_1') | ~r1_tarski('#skF_1', B_2735) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_156377, c_158486])).
% 37.01/26.06  tff(c_158527, plain, (![B_2735]: (k7_relat_1('#skF_1', B_2735)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_156378, c_154332, c_156377, c_158515])).
% 37.01/26.06  tff(c_158293, plain, (![B_2713, A_2714]: (k1_relat_1(k7_relat_1(B_2713, A_2714))=A_2714 | ~r1_tarski(A_2714, k1_relat_1(B_2713)) | ~v1_relat_1(B_2713))), inference(cnfTransformation, [status(thm)], [f_75])).
% 37.01/26.06  tff(c_158304, plain, (![A_2714]: (k1_relat_1(k7_relat_1('#skF_1', A_2714))=A_2714 | ~r1_tarski(A_2714, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_154331, c_158293])).
% 37.01/26.06  tff(c_158308, plain, (![A_2714]: (k1_relat_1(k7_relat_1('#skF_1', A_2714))=A_2714 | ~r1_tarski(A_2714, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_156378, c_158304])).
% 37.01/26.06  tff(c_158529, plain, (![A_2714]: (k1_relat_1('#skF_1')=A_2714 | ~r1_tarski(A_2714, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_158527, c_158308])).
% 37.01/26.06  tff(c_158576, plain, (![A_2737]: (A_2737='#skF_1' | ~r1_tarski(A_2737, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154331, c_158529])).
% 37.01/26.06  tff(c_158596, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_156344, c_158576])).
% 37.01/26.06  tff(c_158638, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_158596, c_154332])).
% 37.01/26.06  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 37.01/26.06  tff(c_154330, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154328, c_154328, c_28])).
% 37.01/26.06  tff(c_158641, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158596, c_158596, c_154330])).
% 37.01/26.06  tff(c_158639, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158596, c_158596, c_154331])).
% 37.01/26.06  tff(c_158762, plain, (![B_2742, A_2743]: (v1_funct_2(B_2742, k1_relat_1(B_2742), A_2743) | ~r1_tarski(k2_relat_1(B_2742), A_2743) | ~v1_funct_1(B_2742) | ~v1_relat_1(B_2742))), inference(cnfTransformation, [status(thm)], [f_145])).
% 37.01/26.06  tff(c_158765, plain, (![A_2743]: (v1_funct_2('#skF_4', '#skF_4', A_2743) | ~r1_tarski(k2_relat_1('#skF_4'), A_2743) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_158639, c_158762])).
% 37.01/26.06  tff(c_158767, plain, (![A_2743]: (v1_funct_2('#skF_4', '#skF_4', A_2743))), inference(demodulation, [status(thm), theory('equality')], [c_157992, c_82, c_158638, c_158641, c_158765])).
% 37.01/26.06  tff(c_158599, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_76, c_158576])).
% 37.01/26.06  tff(c_158653, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158596, c_158599])).
% 37.01/26.06  tff(c_157275, plain, (![C_2595, A_2596, B_2597]: (k7_relat_1(k7_relat_1(C_2595, A_2596), B_2597)=k7_relat_1(C_2595, A_2596) | ~r1_tarski(A_2596, B_2597) | ~v1_relat_1(C_2595))), inference(cnfTransformation, [status(thm)], [f_66])).
% 37.01/26.06  tff(c_157304, plain, (![B_2597]: (k7_relat_1('#skF_1', B_2597)=k7_relat_1('#skF_1', '#skF_1') | ~r1_tarski('#skF_1', B_2597) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_156377, c_157275])).
% 37.01/26.06  tff(c_157316, plain, (![B_2597]: (k7_relat_1('#skF_1', B_2597)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_156378, c_154332, c_156377, c_157304])).
% 37.01/26.06  tff(c_156676, plain, (![B_2542, A_2543]: (k1_relat_1(k7_relat_1(B_2542, A_2543))=A_2543 | ~r1_tarski(A_2543, k1_relat_1(B_2542)) | ~v1_relat_1(B_2542))), inference(cnfTransformation, [status(thm)], [f_75])).
% 37.01/26.06  tff(c_156687, plain, (![A_2543]: (k1_relat_1(k7_relat_1('#skF_1', A_2543))=A_2543 | ~r1_tarski(A_2543, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_154331, c_156676])).
% 37.01/26.06  tff(c_156691, plain, (![A_2543]: (k1_relat_1(k7_relat_1('#skF_1', A_2543))=A_2543 | ~r1_tarski(A_2543, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_156378, c_156687])).
% 37.01/26.06  tff(c_157318, plain, (![A_2543]: (k1_relat_1('#skF_1')=A_2543 | ~r1_tarski(A_2543, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_157316, c_156691])).
% 37.01/26.06  tff(c_157365, plain, (![A_2599]: (A_2599='#skF_1' | ~r1_tarski(A_2599, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154331, c_157318])).
% 37.01/26.06  tff(c_157381, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_156344, c_157365])).
% 37.01/26.06  tff(c_157425, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_157381, c_154332])).
% 37.01/26.06  tff(c_157386, plain, (![B_2597]: (k7_relat_1('#skF_4', B_2597)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157381, c_157381, c_157316])).
% 37.01/26.06  tff(c_157424, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_157381, c_154353])).
% 37.01/26.06  tff(c_157847, plain, (![A_2631, B_2632, C_2633, D_2634]: (k2_partfun1(A_2631, B_2632, C_2633, D_2634)=k7_relat_1(C_2633, D_2634) | ~m1_subset_1(C_2633, k1_zfmisc_1(k2_zfmisc_1(A_2631, B_2632))) | ~v1_funct_1(C_2633))), inference(cnfTransformation, [status(thm)], [f_133])).
% 37.01/26.06  tff(c_157854, plain, (![A_2631, B_2632, D_2634]: (k2_partfun1(A_2631, B_2632, '#skF_4', D_2634)=k7_relat_1('#skF_4', D_2634) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_157424, c_157847])).
% 37.01/26.06  tff(c_157863, plain, (![A_2631, B_2632, D_2634]: (k2_partfun1(A_2631, B_2632, '#skF_4', D_2634)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_157386, c_157854])).
% 37.01/26.06  tff(c_157384, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_76, c_157365])).
% 37.01/26.06  tff(c_157441, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_157381, c_157384])).
% 37.01/26.06  tff(c_18, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 37.01/26.06  tff(c_154485, plain, (![C_2307, A_2308, B_2309]: (v1_relat_1(C_2307) | ~m1_subset_1(C_2307, k1_zfmisc_1(k2_zfmisc_1(A_2308, B_2309))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 37.01/26.06  tff(c_154501, plain, (![C_2310]: (v1_relat_1(C_2310) | ~m1_subset_1(C_2310, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_154363, c_154485])).
% 37.01/26.06  tff(c_154514, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_154391, c_154501])).
% 37.01/26.06  tff(c_154870, plain, (![A_2372, B_2373, C_2374]: (k1_relset_1(A_2372, B_2373, C_2374)=k1_relat_1(C_2374) | ~m1_subset_1(C_2374, k1_zfmisc_1(k2_zfmisc_1(A_2372, B_2373))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 37.01/26.06  tff(c_154901, plain, (![B_2378, C_2379]: (k1_relset_1('#skF_1', B_2378, C_2379)=k1_relat_1(C_2379) | ~m1_subset_1(C_2379, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_154363, c_154870])).
% 37.01/26.06  tff(c_154911, plain, (![B_2378]: (k1_relset_1('#skF_1', B_2378, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_154391, c_154901])).
% 37.01/26.06  tff(c_154347, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154338, c_80])).
% 37.01/26.06  tff(c_56, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 37.01/26.06  tff(c_85, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_56])).
% 37.01/26.06  tff(c_155127, plain, (![B_2402, C_2403]: (k1_relset_1('#skF_1', B_2402, C_2403)='#skF_1' | ~v1_funct_2(C_2403, '#skF_1', B_2402) | ~m1_subset_1(C_2403, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_154328, c_154328, c_154328, c_154328, c_85])).
% 37.01/26.06  tff(c_155132, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_154347, c_155127])).
% 37.01/26.06  tff(c_155139, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154391, c_154911, c_155132])).
% 37.01/26.06  tff(c_34, plain, (![A_19]: (k7_relat_1(A_19, k1_relat_1(A_19))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 37.01/26.06  tff(c_155148, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_155139, c_34])).
% 37.01/26.06  tff(c_155154, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_154514, c_155148])).
% 37.01/26.06  tff(c_155597, plain, (![C_2431, A_2432, B_2433]: (k7_relat_1(k7_relat_1(C_2431, A_2432), B_2433)=k7_relat_1(C_2431, A_2432) | ~r1_tarski(A_2432, B_2433) | ~v1_relat_1(C_2431))), inference(cnfTransformation, [status(thm)], [f_66])).
% 37.01/26.06  tff(c_155650, plain, (![B_2433]: (k7_relat_1('#skF_4', B_2433)=k7_relat_1('#skF_4', '#skF_1') | ~r1_tarski('#skF_1', B_2433) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_155154, c_155597])).
% 37.01/26.06  tff(c_155683, plain, (![B_2433]: (k7_relat_1('#skF_4', B_2433)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_154514, c_154332, c_155154, c_155650])).
% 37.01/26.06  tff(c_154454, plain, (![A_2301, B_2302]: (r1_tarski(A_2301, B_2302) | ~m1_subset_1(A_2301, k1_zfmisc_1(B_2302)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 37.01/26.06  tff(c_154461, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_154391, c_154454])).
% 37.01/26.06  tff(c_154394, plain, (![A_2291]: (k7_relat_1(A_2291, k1_relat_1(A_2291))=A_2291 | ~v1_relat_1(A_2291))), inference(cnfTransformation, [status(thm)], [f_79])).
% 37.01/26.06  tff(c_154403, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_154331, c_154394])).
% 37.01/26.06  tff(c_154406, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_154403])).
% 37.01/26.06  tff(c_154434, plain, (![C_2298, A_2299, B_2300]: (v1_relat_1(C_2298) | ~m1_subset_1(C_2298, k1_zfmisc_1(k2_zfmisc_1(A_2299, B_2300))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 37.01/26.06  tff(c_154446, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_154353, c_154434])).
% 37.01/26.06  tff(c_154451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154406, c_154446])).
% 37.01/26.06  tff(c_154453, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_154403])).
% 37.01/26.06  tff(c_154452, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_154403])).
% 37.01/26.06  tff(c_155653, plain, (![B_2433]: (k7_relat_1('#skF_1', B_2433)=k7_relat_1('#skF_1', '#skF_1') | ~r1_tarski('#skF_1', B_2433) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_154452, c_155597])).
% 37.01/26.06  tff(c_155685, plain, (![B_2433]: (k7_relat_1('#skF_1', B_2433)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154453, c_154332, c_154452, c_155653])).
% 37.01/26.06  tff(c_154752, plain, (![B_2363, A_2364]: (k1_relat_1(k7_relat_1(B_2363, A_2364))=A_2364 | ~r1_tarski(A_2364, k1_relat_1(B_2363)) | ~v1_relat_1(B_2363))), inference(cnfTransformation, [status(thm)], [f_75])).
% 37.01/26.06  tff(c_154763, plain, (![A_2364]: (k1_relat_1(k7_relat_1('#skF_1', A_2364))=A_2364 | ~r1_tarski(A_2364, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_154331, c_154752])).
% 37.01/26.06  tff(c_154767, plain, (![A_2364]: (k1_relat_1(k7_relat_1('#skF_1', A_2364))=A_2364 | ~r1_tarski(A_2364, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154453, c_154763])).
% 37.01/26.06  tff(c_155688, plain, (![A_2364]: (k1_relat_1('#skF_1')=A_2364 | ~r1_tarski(A_2364, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_155685, c_154767])).
% 37.01/26.06  tff(c_155785, plain, (![A_2436]: (A_2436='#skF_1' | ~r1_tarski(A_2436, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154331, c_155688])).
% 37.01/26.06  tff(c_155801, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_154461, c_155785])).
% 37.01/26.06  tff(c_155858, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_155801, c_154353])).
% 37.01/26.06  tff(c_156191, plain, (![A_2452, B_2453, C_2454, D_2455]: (k2_partfun1(A_2452, B_2453, C_2454, D_2455)=k7_relat_1(C_2454, D_2455) | ~m1_subset_1(C_2454, k1_zfmisc_1(k2_zfmisc_1(A_2452, B_2453))) | ~v1_funct_1(C_2454))), inference(cnfTransformation, [status(thm)], [f_133])).
% 37.01/26.06  tff(c_156196, plain, (![A_2452, B_2453, D_2455]: (k2_partfun1(A_2452, B_2453, '#skF_4', D_2455)=k7_relat_1('#skF_4', D_2455) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_155858, c_156191])).
% 37.01/26.06  tff(c_156206, plain, (![A_2452, B_2453, D_2455]: (k2_partfun1(A_2452, B_2453, '#skF_4', D_2455)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_155683, c_156196])).
% 37.01/26.06  tff(c_155804, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_76, c_155785])).
% 37.01/26.06  tff(c_154392, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154338, c_154338, c_154338, c_154355, c_154338, c_154338, c_72])).
% 37.01/26.06  tff(c_154393, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_154392])).
% 37.01/26.06  tff(c_155808, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_155804, c_154393])).
% 37.01/26.06  tff(c_156245, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_155801, c_155801, c_155801, c_155808])).
% 37.01/26.06  tff(c_156326, plain, (~v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156206, c_156245])).
% 37.01/26.06  tff(c_156329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_156326])).
% 37.01/26.06  tff(c_156330, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_154392])).
% 37.01/26.06  tff(c_156379, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_156330])).
% 37.01/26.06  tff(c_156458, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_18, c_156379])).
% 37.01/26.06  tff(c_157411, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157381, c_157381, c_157381, c_156458])).
% 37.01/26.06  tff(c_157956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157425, c_157863, c_157441, c_157411])).
% 37.01/26.06  tff(c_157958, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_156330])).
% 37.01/26.06  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 37.01/26.06  tff(c_158041, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_157958, c_16])).
% 37.01/26.06  tff(c_158595, plain, (k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_158041, c_158576])).
% 37.01/26.06  tff(c_158933, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158653, c_158596, c_158596, c_158596, c_158595])).
% 37.01/26.06  tff(c_157957, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_156330])).
% 37.01/26.06  tff(c_158628, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_158596, c_158596, c_158596, c_157957])).
% 37.01/26.06  tff(c_159091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158767, c_158933, c_158653, c_158653, c_158628])).
% 37.01/26.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.01/26.06  
% 37.01/26.06  Inference rules
% 37.01/26.06  ----------------------
% 37.01/26.06  #Ref     : 0
% 37.01/26.06  #Sup     : 34857
% 37.01/26.06  #Fact    : 0
% 37.01/26.06  #Define  : 0
% 37.01/26.06  #Split   : 35
% 37.01/26.06  #Chain   : 0
% 37.01/26.06  #Close   : 0
% 37.01/26.06  
% 37.01/26.06  Ordering : KBO
% 37.01/26.06  
% 37.01/26.06  Simplification rules
% 37.01/26.06  ----------------------
% 37.01/26.06  #Subsume      : 12819
% 37.01/26.06  #Demod        : 70871
% 37.01/26.06  #Tautology    : 11532
% 37.01/26.06  #SimpNegUnit  : 401
% 37.01/26.06  #BackRed      : 333
% 37.01/26.06  
% 37.01/26.06  #Partial instantiations: 0
% 37.01/26.06  #Strategies tried      : 1
% 37.01/26.06  
% 37.01/26.06  Timing (in seconds)
% 37.01/26.06  ----------------------
% 37.01/26.06  Preprocessing        : 0.36
% 37.01/26.06  Parsing              : 0.20
% 37.01/26.06  CNF conversion       : 0.02
% 37.01/26.06  Main loop            : 24.80
% 37.01/26.06  Inferencing          : 4.10
% 37.01/26.06  Reduction            : 9.88
% 37.01/26.06  Demodulation         : 7.95
% 37.01/26.06  BG Simplification    : 0.39
% 37.01/26.06  Subsumption          : 9.42
% 37.01/26.06  Abstraction          : 0.82
% 37.01/26.06  MUC search           : 0.00
% 37.01/26.06  Cooper               : 0.00
% 37.01/26.06  Total                : 25.24
% 37.01/26.06  Index Insertion      : 0.00
% 37.01/26.06  Index Deletion       : 0.00
% 37.01/26.06  Index Matching       : 0.00
% 37.01/26.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
