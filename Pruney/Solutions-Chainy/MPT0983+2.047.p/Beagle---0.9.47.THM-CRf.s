%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:07 EST 2020

% Result     : Theorem 6.26s
% Output     : CNFRefutation 6.48s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 401 expanded)
%              Number of leaves         :   44 ( 158 expanded)
%              Depth                    :   11
%              Number of atoms          :  216 (1054 expanded)
%              Number of equality atoms :   48 ( 227 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_48,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_142,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_120,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_88,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_42,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    ! [A_4] : k2_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_40,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_111,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_140,plain,(
    ! [A_59] : v1_relat_1(k6_partfun1(A_59)) ),
    inference(resolution,[status(thm)],[c_40,c_111])).

tff(c_6,plain,(
    ! [A_3] :
      ( k2_relat_1(A_3) != k1_xboole_0
      | k1_xboole_0 = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_146,plain,(
    ! [A_59] :
      ( k2_relat_1(k6_partfun1(A_59)) != k1_xboole_0
      | k6_partfun1(A_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_169,plain,(
    ! [A_64] :
      ( k1_xboole_0 != A_64
      | k6_partfun1(A_64) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_146])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_180,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_52])).

tff(c_217,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_14,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_34,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_528,plain,(
    ! [D_100,C_101,A_102,B_103] :
      ( D_100 = C_101
      | ~ r2_relset_1(A_102,B_103,C_101,D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_536,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_528])).

tff(c_551,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_536])).

tff(c_577,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_1372,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_577])).

tff(c_1376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_1372])).

tff(c_1377,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_2278,plain,(
    ! [D_205,A_202,E_206,C_204,B_203] :
      ( k1_xboole_0 = C_204
      | v2_funct_1(D_205)
      | ~ v2_funct_1(k1_partfun1(A_202,B_203,B_203,C_204,D_205,E_206))
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(B_203,C_204)))
      | ~ v1_funct_2(E_206,B_203,C_204)
      | ~ v1_funct_1(E_206)
      | ~ m1_subset_1(D_205,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_2(D_205,A_202,B_203)
      | ~ v1_funct_1(D_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2280,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1377,c_2278])).

tff(c_2282,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_54,c_65,c_2280])).

tff(c_2284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_217,c_2282])).

tff(c_2286,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_194,plain,(
    ! [A_64] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_65])).

tff(c_2304,plain,(
    ! [A_64] :
      ( v2_funct_1('#skF_1')
      | A_64 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2286,c_2286,c_194])).

tff(c_2305,plain,(
    ! [A_64] : A_64 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2304])).

tff(c_2307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2305,c_2286])).

tff(c_2308,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2304])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2294,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2286,c_2])).

tff(c_2309,plain,(
    ! [C_207,A_208,B_209] :
      ( v1_xboole_0(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209)))
      | ~ v1_xboole_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2315,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2309])).

tff(c_2322,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2294,c_2315])).

tff(c_98,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | B_50 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_2333,plain,(
    ! [A_210] :
      ( A_210 = '#skF_1'
      | ~ v1_xboole_0(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2286,c_101])).

tff(c_2340,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2322,c_2333])).

tff(c_2351,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2340,c_88])).

tff(c_2358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2351])).

tff(c_2359,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2383,plain,(
    ! [C_218,A_219,B_220] :
      ( v1_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2395,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2383])).

tff(c_2426,plain,(
    ! [C_222,B_223,A_224] :
      ( v5_relat_1(C_222,B_223)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2438,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_2426])).

tff(c_2683,plain,(
    ! [A_247,B_248,D_249] :
      ( r2_relset_1(A_247,B_248,D_249,D_249)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2690,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_40,c_2683])).

tff(c_2702,plain,(
    ! [A_251,B_252,C_253] :
      ( k2_relset_1(A_251,B_252,C_253) = k2_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2715,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2702])).

tff(c_2757,plain,(
    ! [D_257,C_258,A_259,B_260] :
      ( D_257 = C_258
      | ~ r2_relset_1(A_259,B_260,C_258,D_257)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2763,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_2757])).

tff(c_2774,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2763])).

tff(c_2816,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2774])).

tff(c_3528,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2816])).

tff(c_3532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_58,c_54,c_3528])).

tff(c_3533,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2774])).

tff(c_4613,plain,(
    ! [A_368,B_369,C_370,D_371] :
      ( k2_relset_1(A_368,B_369,C_370) = B_369
      | ~ r2_relset_1(B_369,B_369,k1_partfun1(B_369,A_368,A_368,B_369,D_371,C_370),k6_partfun1(B_369))
      | ~ m1_subset_1(D_371,k1_zfmisc_1(k2_zfmisc_1(B_369,A_368)))
      | ~ v1_funct_2(D_371,B_369,A_368)
      | ~ v1_funct_1(D_371)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(A_368,B_369)))
      | ~ v1_funct_2(C_370,A_368,B_369)
      | ~ v1_funct_1(C_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4622,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3533,c_4613])).

tff(c_4630,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_64,c_62,c_60,c_2690,c_2715,c_4622])).

tff(c_30,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4636,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4630,c_30])).

tff(c_4640,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2438,c_4630,c_4636])).

tff(c_4642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2359,c_4640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.26/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.26/2.27  
% 6.26/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.26/2.27  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.26/2.27  
% 6.26/2.27  %Foreground sorts:
% 6.26/2.27  
% 6.26/2.27  
% 6.26/2.27  %Background operators:
% 6.26/2.27  
% 6.26/2.27  
% 6.26/2.27  %Foreground operators:
% 6.26/2.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.26/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.26/2.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.26/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.26/2.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.26/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.26/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.26/2.27  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.26/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.26/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.26/2.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.26/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.26/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.26/2.27  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.26/2.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.26/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.26/2.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.26/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.26/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.26/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.26/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.26/2.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.26/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.26/2.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.26/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.26/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.26/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.26/2.27  
% 6.48/2.31  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.48/2.31  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.48/2.31  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.48/2.31  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.48/2.31  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.48/2.31  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.48/2.31  tff(f_48, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 6.48/2.31  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.48/2.31  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.48/2.31  tff(f_142, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.48/2.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.48/2.31  tff(f_65, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.48/2.31  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.48/2.31  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.48/2.31  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.48/2.31  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.48/2.31  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.48/2.31  tff(c_50, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.48/2.31  tff(c_88, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 6.48/2.31  tff(c_42, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.48/2.31  tff(c_12, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.48/2.31  tff(c_66, plain, (![A_4]: (k2_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 6.48/2.31  tff(c_40, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.48/2.31  tff(c_111, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.48/2.31  tff(c_140, plain, (![A_59]: (v1_relat_1(k6_partfun1(A_59)))), inference(resolution, [status(thm)], [c_40, c_111])).
% 6.48/2.31  tff(c_6, plain, (![A_3]: (k2_relat_1(A_3)!=k1_xboole_0 | k1_xboole_0=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.48/2.31  tff(c_146, plain, (![A_59]: (k2_relat_1(k6_partfun1(A_59))!=k1_xboole_0 | k6_partfun1(A_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_140, c_6])).
% 6.48/2.31  tff(c_169, plain, (![A_64]: (k1_xboole_0!=A_64 | k6_partfun1(A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_146])).
% 6.48/2.31  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.48/2.31  tff(c_180, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_169, c_52])).
% 6.48/2.31  tff(c_217, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_180])).
% 6.48/2.31  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.48/2.31  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.48/2.31  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.48/2.31  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.48/2.31  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.48/2.31  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.48/2.31  tff(c_14, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.48/2.31  tff(c_65, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 6.48/2.31  tff(c_34, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.48/2.31  tff(c_528, plain, (![D_100, C_101, A_102, B_103]: (D_100=C_101 | ~r2_relset_1(A_102, B_103, C_101, D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.48/2.31  tff(c_536, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_528])).
% 6.48/2.31  tff(c_551, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_536])).
% 6.48/2.31  tff(c_577, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_551])).
% 6.48/2.31  tff(c_1372, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_577])).
% 6.48/2.31  tff(c_1376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_1372])).
% 6.48/2.31  tff(c_1377, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_551])).
% 6.48/2.31  tff(c_2278, plain, (![D_205, A_202, E_206, C_204, B_203]: (k1_xboole_0=C_204 | v2_funct_1(D_205) | ~v2_funct_1(k1_partfun1(A_202, B_203, B_203, C_204, D_205, E_206)) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(B_203, C_204))) | ~v1_funct_2(E_206, B_203, C_204) | ~v1_funct_1(E_206) | ~m1_subset_1(D_205, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~v1_funct_2(D_205, A_202, B_203) | ~v1_funct_1(D_205))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.48/2.31  tff(c_2280, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1377, c_2278])).
% 6.48/2.31  tff(c_2282, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_54, c_65, c_2280])).
% 6.48/2.31  tff(c_2284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_217, c_2282])).
% 6.48/2.31  tff(c_2286, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_180])).
% 6.48/2.31  tff(c_194, plain, (![A_64]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_64)), inference(superposition, [status(thm), theory('equality')], [c_169, c_65])).
% 6.48/2.31  tff(c_2304, plain, (![A_64]: (v2_funct_1('#skF_1') | A_64!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2286, c_2286, c_194])).
% 6.48/2.31  tff(c_2305, plain, (![A_64]: (A_64!='#skF_1')), inference(splitLeft, [status(thm)], [c_2304])).
% 6.48/2.31  tff(c_2307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2305, c_2286])).
% 6.48/2.31  tff(c_2308, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_2304])).
% 6.48/2.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.48/2.31  tff(c_2294, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2286, c_2])).
% 6.48/2.31  tff(c_2309, plain, (![C_207, A_208, B_209]: (v1_xboole_0(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))) | ~v1_xboole_0(A_208))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.48/2.31  tff(c_2315, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2309])).
% 6.48/2.31  tff(c_2322, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2294, c_2315])).
% 6.48/2.31  tff(c_98, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | B_50=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.48/2.31  tff(c_101, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_2, c_98])).
% 6.48/2.31  tff(c_2333, plain, (![A_210]: (A_210='#skF_1' | ~v1_xboole_0(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_2286, c_101])).
% 6.48/2.31  tff(c_2340, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2322, c_2333])).
% 6.48/2.31  tff(c_2351, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2340, c_88])).
% 6.48/2.31  tff(c_2358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2351])).
% 6.48/2.31  tff(c_2359, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 6.48/2.31  tff(c_2383, plain, (![C_218, A_219, B_220]: (v1_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.48/2.31  tff(c_2395, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2383])).
% 6.48/2.31  tff(c_2426, plain, (![C_222, B_223, A_224]: (v5_relat_1(C_222, B_223) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.48/2.31  tff(c_2438, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_2426])).
% 6.48/2.31  tff(c_2683, plain, (![A_247, B_248, D_249]: (r2_relset_1(A_247, B_248, D_249, D_249) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.48/2.31  tff(c_2690, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_40, c_2683])).
% 6.48/2.31  tff(c_2702, plain, (![A_251, B_252, C_253]: (k2_relset_1(A_251, B_252, C_253)=k2_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.48/2.31  tff(c_2715, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2702])).
% 6.48/2.31  tff(c_2757, plain, (![D_257, C_258, A_259, B_260]: (D_257=C_258 | ~r2_relset_1(A_259, B_260, C_258, D_257) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.48/2.31  tff(c_2763, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_2757])).
% 6.48/2.31  tff(c_2774, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2763])).
% 6.48/2.31  tff(c_2816, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2774])).
% 6.48/2.31  tff(c_3528, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2816])).
% 6.48/2.31  tff(c_3532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_58, c_54, c_3528])).
% 6.48/2.31  tff(c_3533, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2774])).
% 6.48/2.31  tff(c_4613, plain, (![A_368, B_369, C_370, D_371]: (k2_relset_1(A_368, B_369, C_370)=B_369 | ~r2_relset_1(B_369, B_369, k1_partfun1(B_369, A_368, A_368, B_369, D_371, C_370), k6_partfun1(B_369)) | ~m1_subset_1(D_371, k1_zfmisc_1(k2_zfmisc_1(B_369, A_368))) | ~v1_funct_2(D_371, B_369, A_368) | ~v1_funct_1(D_371) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(A_368, B_369))) | ~v1_funct_2(C_370, A_368, B_369) | ~v1_funct_1(C_370))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.48/2.31  tff(c_4622, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3533, c_4613])).
% 6.48/2.31  tff(c_4630, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_64, c_62, c_60, c_2690, c_2715, c_4622])).
% 6.48/2.31  tff(c_30, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.48/2.31  tff(c_4636, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4630, c_30])).
% 6.48/2.31  tff(c_4640, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2438, c_4630, c_4636])).
% 6.48/2.31  tff(c_4642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2359, c_4640])).
% 6.48/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.48/2.31  
% 6.48/2.31  Inference rules
% 6.48/2.31  ----------------------
% 6.48/2.31  #Ref     : 8
% 6.48/2.31  #Sup     : 1204
% 6.48/2.31  #Fact    : 0
% 6.48/2.31  #Define  : 0
% 6.48/2.31  #Split   : 28
% 6.48/2.31  #Chain   : 0
% 6.48/2.31  #Close   : 0
% 6.48/2.31  
% 6.48/2.31  Ordering : KBO
% 6.48/2.31  
% 6.48/2.31  Simplification rules
% 6.48/2.31  ----------------------
% 6.48/2.31  #Subsume      : 336
% 6.48/2.31  #Demod        : 370
% 6.48/2.31  #Tautology    : 249
% 6.48/2.31  #SimpNegUnit  : 21
% 6.48/2.31  #BackRed      : 30
% 6.48/2.31  
% 6.48/2.31  #Partial instantiations: 0
% 6.48/2.31  #Strategies tried      : 1
% 6.48/2.31  
% 6.48/2.31  Timing (in seconds)
% 6.48/2.31  ----------------------
% 6.48/2.31  Preprocessing        : 0.36
% 6.48/2.31  Parsing              : 0.19
% 6.48/2.31  CNF conversion       : 0.02
% 6.48/2.31  Main loop            : 1.16
% 6.48/2.31  Inferencing          : 0.36
% 6.48/2.31  Reduction            : 0.40
% 6.48/2.31  Demodulation         : 0.29
% 6.48/2.31  BG Simplification    : 0.04
% 6.48/2.31  Subsumption          : 0.26
% 6.48/2.31  Abstraction          : 0.05
% 6.48/2.31  MUC search           : 0.00
% 6.48/2.31  Cooper               : 0.00
% 6.48/2.31  Total                : 1.58
% 6.48/2.31  Index Insertion      : 0.00
% 6.48/2.31  Index Deletion       : 0.00
% 6.48/2.31  Index Matching       : 0.00
% 6.48/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
