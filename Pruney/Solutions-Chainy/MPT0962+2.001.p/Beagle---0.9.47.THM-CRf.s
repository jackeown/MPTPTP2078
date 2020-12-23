%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:51 EST 2020

% Result     : Theorem 22.68s
% Output     : CNFRefutation 22.99s
% Verified   : 
% Statistics : Number of formulae       :  282 (1802 expanded)
%              Number of leaves         :   43 ( 615 expanded)
%              Depth                    :   18
%              Number of atoms          :  602 (4573 expanded)
%              Number of equality atoms :  163 (1575 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_153,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_100,axiom,
    ( v1_relat_1(k1_wellord2(k1_xboole_0))
    & v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_wellord2)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_81,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_108,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_relat_1(k1_wellord2(A))
        & ~ v1_xboole_0(k1_wellord2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_wellord2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_74,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_66,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_46),k2_relat_1(A_46))))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_79542,plain,(
    ! [D_2952,C_2953,B_2954,A_2955] :
      ( m1_subset_1(D_2952,k1_zfmisc_1(k2_zfmisc_1(C_2953,B_2954)))
      | ~ r1_tarski(k2_relat_1(D_2952),B_2954)
      | ~ m1_subset_1(D_2952,k1_zfmisc_1(k2_zfmisc_1(C_2953,A_2955))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_82532,plain,(
    ! [A_3109,B_3110] :
      ( m1_subset_1(A_3109,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_3109),B_3110)))
      | ~ r1_tarski(k2_relat_1(A_3109),B_3110)
      | ~ v1_funct_1(A_3109)
      | ~ v1_relat_1(A_3109) ) ),
    inference(resolution,[status(thm)],[c_66,c_79542])).

tff(c_42,plain,(
    v1_relat_1(k1_wellord2(k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_175,plain,(
    ! [A_66] :
      ( k2_relat_1(A_66) != k1_xboole_0
      | k1_xboole_0 = A_66
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_194,plain,
    ( k2_relat_1(k1_wellord2(k1_xboole_0)) != k1_xboole_0
    | k1_wellord2(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_175])).

tff(c_234,plain,(
    k2_relat_1(k1_wellord2(k1_xboole_0)) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_28,plain,(
    ! [A_18] : k1_relat_1('#skF_1'(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [A_18] : v1_relat_1('#skF_1'(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_129,plain,(
    ! [A_64] :
      ( k1_relat_1(A_64) != k1_xboole_0
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_138,plain,(
    ! [A_18] :
      ( k1_relat_1('#skF_1'(A_18)) != k1_xboole_0
      | '#skF_1'(A_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_129])).

tff(c_152,plain,(
    ! [A_65] :
      ( k1_xboole_0 != A_65
      | '#skF_1'(A_65) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_138])).

tff(c_162,plain,(
    ! [A_65] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_32])).

tff(c_196,plain,(
    ! [A_65] : k1_xboole_0 != A_65 ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_102,plain,(
    ! [A_57,B_58] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_57,B_58)),B_58) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [A_57] : k2_relat_1(k2_zfmisc_1(A_57,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_107])).

tff(c_203,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_216,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_28])).

tff(c_14,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_414,plain,(
    ! [A_98,B_99] :
      ( k2_relat_1(k2_zfmisc_1(A_98,B_99)) != k1_xboole_0
      | k2_zfmisc_1(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_175])).

tff(c_418,plain,(
    ! [A_57] : k2_zfmisc_1(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_414])).

tff(c_419,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_107])).

tff(c_148,plain,(
    ! [A_18] :
      ( k1_xboole_0 != A_18
      | '#skF_1'(A_18) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_138])).

tff(c_30,plain,(
    ! [A_18] : v1_funct_1('#skF_1'(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_369,plain,(
    ! [A_90] :
      ( m1_subset_1(A_90,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_90),k2_relat_1(A_90))))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_384,plain,(
    ! [A_18] :
      ( m1_subset_1('#skF_1'(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,k2_relat_1('#skF_1'(A_18)))))
      | ~ v1_funct_1('#skF_1'(A_18))
      | ~ v1_relat_1('#skF_1'(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_369])).

tff(c_574,plain,(
    ! [A_113] : m1_subset_1('#skF_1'(A_113),k1_zfmisc_1(k2_zfmisc_1(A_113,k2_relat_1('#skF_1'(A_113))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_384])).

tff(c_592,plain,(
    ! [A_18] :
      ( m1_subset_1('#skF_1'(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,k2_relat_1(k1_xboole_0))))
      | k1_xboole_0 != A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_574])).

tff(c_604,plain,(
    ! [A_115] :
      ( m1_subset_1('#skF_1'(A_115),k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != A_115 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_419,c_592])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_617,plain,(
    ! [A_115] :
      ( r1_tarski('#skF_1'(A_115),k1_xboole_0)
      | k1_xboole_0 != A_115 ) ),
    inference(resolution,[status(thm)],[c_604,c_8])).

tff(c_521,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(k1_relat_1(A_103),k1_relat_1(B_104))
      | ~ r1_tarski(A_103,B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_527,plain,(
    ! [A_18,B_104] :
      ( r1_tarski(A_18,k1_relat_1(B_104))
      | ~ r1_tarski('#skF_1'(A_18),B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1('#skF_1'(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_521])).

tff(c_1103,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(A_166,k1_relat_1(B_167))
      | ~ r1_tarski('#skF_1'(A_166),B_167)
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_527])).

tff(c_1109,plain,(
    ! [A_115] :
      ( r1_tarski(A_115,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_115 ) ),
    inference(resolution,[status(thm)],[c_617,c_1103])).

tff(c_1136,plain,(
    ! [A_168] :
      ( r1_tarski(A_168,k1_xboole_0)
      | k1_xboole_0 != A_168 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_216,c_1109])).

tff(c_493,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(k2_relat_1(A_101),k2_relat_1(B_102))
      | ~ r1_tarski(A_101,B_102)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_502,plain,(
    ! [A_101] :
      ( r1_tarski(k2_relat_1(A_101),k1_xboole_0)
      | ~ r1_tarski(A_101,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_493])).

tff(c_862,plain,(
    ! [A_151] :
      ( r1_tarski(k2_relat_1(A_151),k1_xboole_0)
      | ~ r1_tarski(A_151,k1_xboole_0)
      | ~ v1_relat_1(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_502])).

tff(c_875,plain,(
    ! [A_151] :
      ( k2_relat_1(A_151) = k1_xboole_0
      | ~ r1_tarski(A_151,k1_xboole_0)
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_862,c_2])).

tff(c_1333,plain,(
    ! [A_181] :
      ( k2_relat_1(A_181) = k1_xboole_0
      | ~ v1_relat_1(A_181)
      | k1_xboole_0 != A_181 ) ),
    inference(resolution,[status(thm)],[c_1136,c_875])).

tff(c_1348,plain,
    ( k2_relat_1(k1_wellord2(k1_xboole_0)) = k1_xboole_0
    | k1_wellord2(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1333])).

tff(c_1359,plain,(
    k1_wellord2(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_1348])).

tff(c_40,plain,(
    v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_151,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_138])).

tff(c_530,plain,(
    ! [A_103,A_18] :
      ( r1_tarski(k1_relat_1(A_103),A_18)
      | ~ r1_tarski(A_103,'#skF_1'(A_18))
      | ~ v1_relat_1('#skF_1'(A_18))
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_521])).

tff(c_1269,plain,(
    ! [A_173,A_174] :
      ( r1_tarski(k1_relat_1(A_173),A_174)
      | ~ r1_tarski(A_173,'#skF_1'(A_174))
      | ~ v1_relat_1(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_530])).

tff(c_1287,plain,(
    ! [A_18,A_174] :
      ( r1_tarski(A_18,A_174)
      | ~ r1_tarski('#skF_1'(A_18),'#skF_1'(A_174))
      | ~ v1_relat_1('#skF_1'(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1269])).

tff(c_1556,plain,(
    ! [A_195,A_196] :
      ( r1_tarski(A_195,A_196)
      | ~ r1_tarski('#skF_1'(A_195),'#skF_1'(A_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1287])).

tff(c_2020,plain,(
    ! [A_212,A_213] :
      ( r1_tarski(A_212,A_213)
      | ~ r1_tarski('#skF_1'(A_212),k1_xboole_0)
      | k1_xboole_0 != A_213 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_1556])).

tff(c_2033,plain,(
    ! [A_115,A_213] :
      ( r1_tarski(A_115,A_213)
      | k1_xboole_0 != A_213
      | k1_xboole_0 != A_115 ) ),
    inference(resolution,[status(thm)],[c_617,c_2020])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_344,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_partfun1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_349,plain,(
    ! [A_7,A_87,B_88] :
      ( v1_partfun1(A_7,A_87)
      | ~ v1_xboole_0(A_87)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_10,c_344])).

tff(c_7303,plain,(
    ! [A_427,A_428,B_429] :
      ( v1_partfun1(k1_relat_1(A_427),A_428)
      | ~ v1_xboole_0(A_428)
      | ~ r1_tarski(A_427,'#skF_1'(k2_zfmisc_1(A_428,B_429)))
      | ~ v1_relat_1(A_427) ) ),
    inference(resolution,[status(thm)],[c_1269,c_349])).

tff(c_7326,plain,(
    ! [A_427,A_57] :
      ( v1_partfun1(k1_relat_1(A_427),A_57)
      | ~ v1_xboole_0(A_57)
      | ~ r1_tarski(A_427,'#skF_1'(k1_xboole_0))
      | ~ v1_relat_1(A_427) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_7303])).

tff(c_7341,plain,(
    ! [A_430,A_431] :
      ( v1_partfun1(k1_relat_1(A_430),A_431)
      | ~ v1_xboole_0(A_431)
      | ~ r1_tarski(A_430,k1_xboole_0)
      | ~ v1_relat_1(A_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_7326])).

tff(c_7350,plain,(
    ! [A_18,A_431] :
      ( v1_partfun1(A_18,A_431)
      | ~ v1_xboole_0(A_431)
      | ~ r1_tarski('#skF_1'(A_18),k1_xboole_0)
      | ~ v1_relat_1('#skF_1'(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7341])).

tff(c_7357,plain,(
    ! [A_432,A_433] :
      ( v1_partfun1(A_432,A_433)
      | ~ v1_xboole_0(A_433)
      | ~ r1_tarski('#skF_1'(A_432),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_7350])).

tff(c_7390,plain,(
    ! [A_432,A_433] :
      ( v1_partfun1(A_432,A_433)
      | ~ v1_xboole_0(A_433)
      | '#skF_1'(A_432) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2033,c_7357])).

tff(c_265,plain,(
    ! [A_75] :
      ( k2_xboole_0(k1_relat_1(A_75),k2_relat_1(A_75)) = k3_relat_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(A_2,k2_xboole_0(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_291,plain,(
    ! [A_78] :
      ( r1_tarski(k1_relat_1(A_78),k3_relat_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_4])).

tff(c_297,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k3_relat_1('#skF_1'(A_18)))
      | ~ v1_relat_1('#skF_1'(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_291])).

tff(c_301,plain,(
    ! [A_79] : r1_tarski(A_79,k3_relat_1('#skF_1'(A_79))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_297])).

tff(c_324,plain,(
    r1_tarski(k1_xboole_0,k3_relat_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_301])).

tff(c_160,plain,(
    ! [A_65] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_30])).

tff(c_168,plain,(
    ! [A_65] : k1_xboole_0 != A_65 ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_107])).

tff(c_174,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_108,plain,(
    ! [A_59] : k2_relat_1(k2_zfmisc_1(A_59,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_12,B_13)),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_16])).

tff(c_54,plain,(
    ! [A_43] :
      ( v1_funct_2(k1_xboole_0,A_43,k1_xboole_0)
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_43,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_468,plain,(
    ! [A_43] :
      ( v1_funct_2(k1_xboole_0,A_43,k1_xboole_0)
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_54])).

tff(c_469,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_468])).

tff(c_473,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_469])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_473])).

tff(c_479,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_468])).

tff(c_797,plain,(
    ! [D_138,C_139,B_140,A_141] :
      ( m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(C_139,B_140)))
      | ~ r1_tarski(k2_relat_1(D_138),B_140)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(C_139,A_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11732,plain,(
    ! [D_543,A_544,B_545] :
      ( m1_subset_1(D_543,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545)))
      | ~ r1_tarski(k2_relat_1(D_543),B_545)
      | ~ m1_subset_1(D_543,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_797])).

tff(c_12126,plain,(
    ! [D_554,A_555,B_556] :
      ( r1_tarski(D_554,k2_zfmisc_1(A_555,B_556))
      | ~ r1_tarski(k2_relat_1(D_554),B_556)
      | ~ m1_subset_1(D_554,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_11732,c_8])).

tff(c_12208,plain,(
    ! [A_555,B_556] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_555,B_556))
      | ~ r1_tarski(k1_xboole_0,B_556)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_12126])).

tff(c_12257,plain,(
    ! [A_557,B_558] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_557,B_558))
      | ~ r1_tarski(k1_xboole_0,B_558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_12208])).

tff(c_724,plain,(
    ! [C_128,A_129,B_130] :
      ( v1_funct_2(C_128,A_129,B_130)
      | ~ v1_partfun1(C_128,A_129)
      | ~ v1_funct_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_742,plain,(
    ! [A_7,A_129,B_130] :
      ( v1_funct_2(A_7,A_129,B_130)
      | ~ v1_partfun1(A_7,A_129)
      | ~ v1_funct_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_129,B_130)) ) ),
    inference(resolution,[status(thm)],[c_10,c_724])).

tff(c_12275,plain,(
    ! [A_557,B_558] :
      ( v1_funct_2(k1_xboole_0,A_557,B_558)
      | ~ v1_partfun1(k1_xboole_0,A_557)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_558) ) ),
    inference(resolution,[status(thm)],[c_12257,c_742])).

tff(c_12306,plain,(
    ! [A_557,B_558] :
      ( v1_funct_2(k1_xboole_0,A_557,B_558)
      | ~ v1_partfun1(k1_xboole_0,A_557)
      | ~ r1_tarski(k1_xboole_0,B_558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_12275])).

tff(c_96,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(k1_wellord2(A_54))
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_100,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_239,plain,(
    ! [B_71,A_72] :
      ( v1_xboole_0(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_243,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(A_7)
      | ~ v1_xboole_0(B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_239])).

tff(c_1146,plain,(
    ! [A_168] :
      ( v1_xboole_0(A_168)
      | ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 != A_168 ) ),
    inference(resolution,[status(thm)],[c_1136,c_243])).

tff(c_1160,plain,(
    ! [A_169] :
      ( v1_xboole_0(A_169)
      | k1_xboole_0 != A_169 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1146])).

tff(c_320,plain,(
    ! [A_81] :
      ( v1_xboole_0(A_81)
      | ~ v1_xboole_0(k3_relat_1('#skF_1'(A_81))) ) ),
    inference(resolution,[status(thm)],[c_301,c_243])).

tff(c_323,plain,(
    ! [A_18] :
      ( v1_xboole_0(A_18)
      | ~ v1_xboole_0(k3_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_320])).

tff(c_343,plain,(
    ~ v1_xboole_0(k3_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_1184,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1160,c_343])).

tff(c_307,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k3_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_301])).

tff(c_404,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_413,plain,(
    ! [A_95,B_96,A_7] :
      ( k1_relset_1(A_95,B_96,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_95,B_96)) ) ),
    inference(resolution,[status(thm)],[c_10,c_404])).

tff(c_12286,plain,(
    ! [A_557,B_558] :
      ( k1_relset_1(A_557,B_558,k1_xboole_0) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_558) ) ),
    inference(resolution,[status(thm)],[c_12257,c_413])).

tff(c_12316,plain,(
    ! [A_559,B_560] :
      ( k1_relset_1(A_559,B_560,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_12286])).

tff(c_12464,plain,(
    ! [A_559] : k1_relset_1(A_559,k3_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_307,c_12316])).

tff(c_280,plain,(
    ! [A_18] :
      ( k2_xboole_0(A_18,k2_relat_1('#skF_1'(A_18))) = k3_relat_1('#skF_1'(A_18))
      | ~ v1_relat_1('#skF_1'(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_265])).

tff(c_350,plain,(
    ! [A_89] : k2_xboole_0(A_89,k2_relat_1('#skF_1'(A_89))) = k3_relat_1('#skF_1'(A_89)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_280])).

tff(c_365,plain,(
    ! [A_18] :
      ( k2_xboole_0(A_18,k2_relat_1(k1_xboole_0)) = k3_relat_1('#skF_1'(A_18))
      | k1_xboole_0 != A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_350])).

tff(c_751,plain,(
    ! [A_132] :
      ( k3_relat_1('#skF_1'(A_132)) = k2_xboole_0(A_132,k1_xboole_0)
      | k1_xboole_0 != A_132 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_365])).

tff(c_772,plain,(
    ! [A_18] :
      ( k2_xboole_0(A_18,k1_xboole_0) = k3_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_18
      | k1_xboole_0 != A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_751])).

tff(c_13234,plain,(
    ! [D_574,A_575,B_576] :
      ( r1_tarski(D_574,k2_zfmisc_1(A_575,k2_xboole_0(k2_relat_1(D_574),B_576)))
      | ~ m1_subset_1(D_574,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_12126])).

tff(c_13323,plain,(
    ! [A_575,B_576] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_575,k2_xboole_0(k1_xboole_0,B_576)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_13234])).

tff(c_13355,plain,(
    ! [A_577,B_578] : r1_tarski(k1_xboole_0,k2_zfmisc_1(A_577,k2_xboole_0(k1_xboole_0,B_578))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_13323])).

tff(c_13431,plain,(
    ! [A_579] : r1_tarski(k1_xboole_0,k2_zfmisc_1(A_579,k3_relat_1(k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_13355])).

tff(c_1045,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1064,plain,(
    ! [B_159,A_160,A_7] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,A_7) = A_160
      | ~ v1_funct_2(A_7,A_160,B_159)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_160,B_159)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1045])).

tff(c_13436,plain,(
    ! [A_579] :
      ( k3_relat_1(k1_xboole_0) = k1_xboole_0
      | k1_relset_1(A_579,k3_relat_1(k1_xboole_0),k1_xboole_0) = A_579
      | ~ v1_funct_2(k1_xboole_0,A_579,k3_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_13431,c_1064])).

tff(c_13466,plain,(
    ! [A_579] :
      ( k3_relat_1(k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 = A_579
      | ~ v1_funct_2(k1_xboole_0,A_579,k3_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12464,c_13436])).

tff(c_13526,plain,(
    ! [A_582] :
      ( k1_xboole_0 = A_582
      | ~ v1_funct_2(k1_xboole_0,A_582,k3_relat_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1184,c_13466])).

tff(c_13530,plain,(
    ! [A_557] :
      ( k1_xboole_0 = A_557
      | ~ v1_partfun1(k1_xboole_0,A_557)
      | ~ r1_tarski(k1_xboole_0,k3_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12306,c_13526])).

tff(c_13558,plain,(
    ! [A_583] :
      ( k1_xboole_0 = A_583
      | ~ v1_partfun1(k1_xboole_0,A_583) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_13530])).

tff(c_13565,plain,(
    ! [A_433] :
      ( k1_xboole_0 = A_433
      | ~ v1_xboole_0(A_433)
      | '#skF_1'(k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7390,c_13558])).

tff(c_13610,plain,(
    ! [A_584] :
      ( k1_xboole_0 = A_584
      | ~ v1_xboole_0(A_584) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_13565])).

tff(c_13646,plain,(
    k1_wellord2(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_13610])).

tff(c_13661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1359,c_13646])).

tff(c_13672,plain,(
    ! [A_588] :
      ( v1_xboole_0(A_588)
      | k1_xboole_0 != A_588 ) ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_245,plain,(
    ! [A_73,B_74] :
      ( v1_xboole_0(A_73)
      | ~ v1_xboole_0(B_74)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_10,c_239])).

tff(c_263,plain,
    ( v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_245])).

tff(c_264,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_13687,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(resolution,[status(thm)],[c_13672,c_264])).

tff(c_14132,plain,(
    ! [D_639,C_640,B_641,A_642] :
      ( m1_subset_1(D_639,k1_zfmisc_1(k2_zfmisc_1(C_640,B_641)))
      | ~ r1_tarski(k2_relat_1(D_639),B_641)
      | ~ m1_subset_1(D_639,k1_zfmisc_1(k2_zfmisc_1(C_640,A_642))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_17197,plain,(
    ! [A_801,B_802] :
      ( m1_subset_1(A_801,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_801),B_802)))
      | ~ r1_tarski(k2_relat_1(A_801),B_802)
      | ~ v1_funct_1(A_801)
      | ~ v1_relat_1(A_801) ) ),
    inference(resolution,[status(thm)],[c_66,c_14132])).

tff(c_34,plain,(
    ! [A_24,B_25,C_26] :
      ( k1_relset_1(A_24,B_25,C_26) = k1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34333,plain,(
    ! [A_1287,B_1288] :
      ( k1_relset_1(k1_relat_1(A_1287),B_1288,A_1287) = k1_relat_1(A_1287)
      | ~ r1_tarski(k2_relat_1(A_1287),B_1288)
      | ~ v1_funct_1(A_1287)
      | ~ v1_relat_1(A_1287) ) ),
    inference(resolution,[status(thm)],[c_17197,c_34])).

tff(c_34413,plain,
    ( k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_34333])).

tff(c_34453,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_34413])).

tff(c_60,plain,(
    ! [B_44,C_45,A_43] :
      ( k1_xboole_0 = B_44
      | v1_funct_2(C_45,A_43,B_44)
      | k1_relset_1(A_43,B_44,C_45) != A_43
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44092,plain,(
    ! [B_1574,A_1575] :
      ( k1_xboole_0 = B_1574
      | v1_funct_2(A_1575,k1_relat_1(A_1575),B_1574)
      | k1_relset_1(k1_relat_1(A_1575),B_1574,A_1575) != k1_relat_1(A_1575)
      | ~ r1_tarski(k2_relat_1(A_1575),B_1574)
      | ~ v1_funct_1(A_1575)
      | ~ v1_relat_1(A_1575) ) ),
    inference(resolution,[status(thm)],[c_17197,c_60])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72])).

tff(c_93,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_44106,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44092,c_93])).

tff(c_44127,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_34453,c_44106])).

tff(c_44129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13687,c_44127])).

tff(c_44130,plain,(
    v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_44247,plain,(
    ! [A_1594,B_1595] :
      ( r1_tarski(k2_relat_1(A_1594),k2_relat_1(B_1595))
      | ~ r1_tarski(A_1594,B_1595)
      | ~ v1_relat_1(B_1595)
      | ~ v1_relat_1(A_1594) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_49472,plain,(
    ! [A_1872,B_1873] :
      ( v1_xboole_0(k2_relat_1(A_1872))
      | ~ v1_xboole_0(k2_relat_1(B_1873))
      | ~ r1_tarski(A_1872,B_1873)
      | ~ v1_relat_1(B_1873)
      | ~ v1_relat_1(A_1872) ) ),
    inference(resolution,[status(thm)],[c_44247,c_243])).

tff(c_49499,plain,(
    ! [A_1872] :
      ( v1_xboole_0(k2_relat_1(A_1872))
      | ~ r1_tarski(A_1872,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_1872) ) ),
    inference(resolution,[status(thm)],[c_44130,c_49472])).

tff(c_49522,plain,(
    ! [A_1874] :
      ( v1_xboole_0(k2_relat_1(A_1874))
      | ~ r1_tarski(A_1874,'#skF_3')
      | ~ v1_relat_1(A_1874) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_49499])).

tff(c_44257,plain,(
    ! [A_1594,B_1595] :
      ( v1_xboole_0(k2_relat_1(A_1594))
      | ~ v1_xboole_0(k2_relat_1(B_1595))
      | ~ r1_tarski(A_1594,B_1595)
      | ~ v1_relat_1(B_1595)
      | ~ v1_relat_1(A_1594) ) ),
    inference(resolution,[status(thm)],[c_44247,c_243])).

tff(c_49653,plain,(
    ! [A_1881,A_1882] :
      ( v1_xboole_0(k2_relat_1(A_1881))
      | ~ r1_tarski(A_1881,A_1882)
      | ~ v1_relat_1(A_1881)
      | ~ r1_tarski(A_1882,'#skF_3')
      | ~ v1_relat_1(A_1882) ) ),
    inference(resolution,[status(thm)],[c_49522,c_44257])).

tff(c_49793,plain,
    ( v1_xboole_0(k2_relat_1(k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_49653])).

tff(c_50141,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_49793])).

tff(c_44847,plain,(
    ! [D_1651,C_1652,B_1653,A_1654] :
      ( m1_subset_1(D_1651,k1_zfmisc_1(k2_zfmisc_1(C_1652,B_1653)))
      | ~ r1_tarski(k2_relat_1(D_1651),B_1653)
      | ~ m1_subset_1(D_1651,k1_zfmisc_1(k2_zfmisc_1(C_1652,A_1654))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48258,plain,(
    ! [A_1823,B_1824] :
      ( m1_subset_1(A_1823,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1823),B_1824)))
      | ~ r1_tarski(k2_relat_1(A_1823),B_1824)
      | ~ v1_funct_1(A_1823)
      | ~ v1_relat_1(A_1823) ) ),
    inference(resolution,[status(thm)],[c_66,c_44847])).

tff(c_52884,plain,(
    ! [A_1980,B_1981] :
      ( k1_relset_1(k1_relat_1(A_1980),B_1981,A_1980) = k1_relat_1(A_1980)
      | ~ r1_tarski(k2_relat_1(A_1980),B_1981)
      | ~ v1_funct_1(A_1980)
      | ~ v1_relat_1(A_1980) ) ),
    inference(resolution,[status(thm)],[c_48258,c_34])).

tff(c_52979,plain,
    ( k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_52884])).

tff(c_53024,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_52979])).

tff(c_61239,plain,(
    ! [B_2226,A_2227] :
      ( k1_xboole_0 = B_2226
      | v1_funct_2(A_2227,k1_relat_1(A_2227),B_2226)
      | k1_relset_1(k1_relat_1(A_2227),B_2226,A_2227) != k1_relat_1(A_2227)
      | ~ r1_tarski(k2_relat_1(A_2227),B_2226)
      | ~ v1_funct_1(A_2227)
      | ~ v1_relat_1(A_2227) ) ),
    inference(resolution,[status(thm)],[c_48258,c_60])).

tff(c_61245,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61239,c_93])).

tff(c_61259,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_53024,c_61245])).

tff(c_61559,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61259,c_203])).

tff(c_61568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50141,c_61559])).

tff(c_61570,plain,(
    v1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_49793])).

tff(c_44279,plain,(
    ! [A_1601,B_1602] :
      ( k2_relat_1(k2_zfmisc_1(A_1601,B_1602)) != k1_xboole_0
      | k2_zfmisc_1(A_1601,B_1602) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_175])).

tff(c_44283,plain,(
    ! [A_57] : k2_zfmisc_1(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_44279])).

tff(c_44284,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44283,c_107])).

tff(c_44394,plain,(
    ! [A_1611] :
      ( m1_subset_1(A_1611,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1611),k2_relat_1(A_1611))))
      | ~ v1_funct_1(A_1611)
      | ~ v1_relat_1(A_1611) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44412,plain,(
    ! [A_18] :
      ( m1_subset_1('#skF_1'(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,k2_relat_1('#skF_1'(A_18)))))
      | ~ v1_funct_1('#skF_1'(A_18))
      | ~ v1_relat_1('#skF_1'(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_44394])).

tff(c_44421,plain,(
    ! [A_1612] : m1_subset_1('#skF_1'(A_1612),k1_zfmisc_1(k2_zfmisc_1(A_1612,k2_relat_1('#skF_1'(A_1612))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_44412])).

tff(c_44439,plain,(
    ! [A_18] :
      ( m1_subset_1('#skF_1'(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,k2_relat_1(k1_xboole_0))))
      | k1_xboole_0 != A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_44421])).

tff(c_44451,plain,(
    ! [A_1614] :
      ( m1_subset_1('#skF_1'(A_1614),k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != A_1614 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44283,c_44284,c_44439])).

tff(c_44464,plain,(
    ! [A_1614] :
      ( r1_tarski('#skF_1'(A_1614),k1_xboole_0)
      | k1_xboole_0 != A_1614 ) ),
    inference(resolution,[status(thm)],[c_44451,c_8])).

tff(c_44264,plain,(
    ! [A_1599,B_1600] :
      ( r1_tarski(k1_relat_1(A_1599),k1_relat_1(B_1600))
      | ~ r1_tarski(A_1599,B_1600)
      | ~ v1_relat_1(B_1600)
      | ~ v1_relat_1(A_1599) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44270,plain,(
    ! [A_18,B_1600] :
      ( r1_tarski(A_18,k1_relat_1(B_1600))
      | ~ r1_tarski('#skF_1'(A_18),B_1600)
      | ~ v1_relat_1(B_1600)
      | ~ v1_relat_1('#skF_1'(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_44264])).

tff(c_44921,plain,(
    ! [A_1661,B_1662] :
      ( r1_tarski(A_1661,k1_relat_1(B_1662))
      | ~ r1_tarski('#skF_1'(A_1661),B_1662)
      | ~ v1_relat_1(B_1662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44270])).

tff(c_44927,plain,(
    ! [A_1614] :
      ( r1_tarski(A_1614,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_1614 ) ),
    inference(resolution,[status(thm)],[c_44464,c_44921])).

tff(c_44948,plain,(
    ! [A_1614] :
      ( r1_tarski(A_1614,k1_xboole_0)
      | k1_xboole_0 != A_1614 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_216,c_44927])).

tff(c_44273,plain,(
    ! [A_1599,A_18] :
      ( r1_tarski(k1_relat_1(A_1599),A_18)
      | ~ r1_tarski(A_1599,'#skF_1'(A_18))
      | ~ v1_relat_1('#skF_1'(A_18))
      | ~ v1_relat_1(A_1599) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_44264])).

tff(c_45105,plain,(
    ! [A_1673,A_1674] :
      ( r1_tarski(k1_relat_1(A_1673),A_1674)
      | ~ r1_tarski(A_1673,'#skF_1'(A_1674))
      | ~ v1_relat_1(A_1673) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44273])).

tff(c_45116,plain,(
    ! [A_1673] :
      ( k1_relat_1(A_1673) = k1_xboole_0
      | ~ r1_tarski(A_1673,'#skF_1'(k1_xboole_0))
      | ~ v1_relat_1(A_1673) ) ),
    inference(resolution,[status(thm)],[c_45105,c_2])).

tff(c_45435,plain,(
    ! [A_1696] :
      ( k1_relat_1(A_1696) = k1_xboole_0
      | ~ r1_tarski(A_1696,k1_xboole_0)
      | ~ v1_relat_1(A_1696) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_45116])).

tff(c_45459,plain,(
    ! [A_1614] :
      ( k1_relat_1(A_1614) = k1_xboole_0
      | ~ v1_relat_1(A_1614)
      | k1_xboole_0 != A_1614 ) ),
    inference(resolution,[status(thm)],[c_44948,c_45435])).

tff(c_61591,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k1_xboole_0 != '#skF_2' ),
    inference(resolution,[status(thm)],[c_61570,c_45459])).

tff(c_61595,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_61591])).

tff(c_63988,plain,(
    ! [A_2307,B_2308] :
      ( k1_relset_1(k1_relat_1(A_2307),B_2308,A_2307) = k1_relat_1(A_2307)
      | ~ r1_tarski(k2_relat_1(A_2307),B_2308)
      | ~ v1_funct_1(A_2307)
      | ~ v1_relat_1(A_2307) ) ),
    inference(resolution,[status(thm)],[c_48258,c_34])).

tff(c_64080,plain,
    ( k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_63988])).

tff(c_64124,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64080])).

tff(c_72637,plain,(
    ! [B_2559,A_2560] :
      ( k1_xboole_0 = B_2559
      | v1_funct_2(A_2560,k1_relat_1(A_2560),B_2559)
      | k1_relset_1(k1_relat_1(A_2560),B_2559,A_2560) != k1_relat_1(A_2560)
      | ~ r1_tarski(k2_relat_1(A_2560),B_2559)
      | ~ v1_funct_1(A_2560)
      | ~ v1_relat_1(A_2560) ) ),
    inference(resolution,[status(thm)],[c_48258,c_60])).

tff(c_72643,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72637,c_93])).

tff(c_72657,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_64124,c_72643])).

tff(c_72659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61595,c_72657])).

tff(c_72661,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_61591])).

tff(c_195,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_175])).

tff(c_215,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_72823,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72661,c_215])).

tff(c_73366,plain,(
    ! [A_2567] :
      ( A_2567 = '#skF_2'
      | ~ r1_tarski(A_2567,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72661,c_72661,c_2])).

tff(c_73380,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_74,c_73366])).

tff(c_73390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72823,c_73380])).

tff(c_73391,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_158,plain,(
    ! [A_65] :
      ( k1_relat_1(k1_xboole_0) = A_65
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_28])).

tff(c_73483,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73391,c_73391,c_158])).

tff(c_150,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_129])).

tff(c_204,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_73393,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73391,c_204])).

tff(c_73487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73483,c_73393])).

tff(c_73488,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_73495,plain,(
    ! [A_57] : k2_relat_1(k2_zfmisc_1(A_57,'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73488,c_73488,c_107])).

tff(c_192,plain,(
    ! [A_10,B_11] :
      ( k2_relat_1(k2_zfmisc_1(A_10,B_11)) != k1_xboole_0
      | k2_zfmisc_1(A_10,B_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_175])).

tff(c_74392,plain,(
    ! [A_2655,B_2656] :
      ( k2_relat_1(k2_zfmisc_1(A_2655,B_2656)) != '#skF_3'
      | k2_zfmisc_1(A_2655,B_2656) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73488,c_73488,c_192])).

tff(c_74396,plain,(
    ! [A_57] : k2_zfmisc_1(A_57,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_73495,c_74392])).

tff(c_74399,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74396,c_73495])).

tff(c_74441,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74399,c_74])).

tff(c_73496,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73488,c_100])).

tff(c_73489,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_73507,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73488,c_73489])).

tff(c_73685,plain,(
    ! [A_2593] :
      ( m1_subset_1(A_2593,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2593),k2_relat_1(A_2593))))
      | ~ v1_funct_1(A_2593)
      | ~ v1_relat_1(A_2593) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_73700,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_73507,c_73685])).

tff(c_73710,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_73700])).

tff(c_52,plain,(
    ! [C_42,A_39,B_40] :
      ( v1_partfun1(C_42,A_39)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_73827,plain,
    ( v1_partfun1('#skF_3','#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_73710,c_52])).

tff(c_73836,plain,(
    v1_partfun1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73496,c_73827])).

tff(c_74725,plain,(
    ! [D_2679,C_2680,B_2681,A_2682] :
      ( m1_subset_1(D_2679,k1_zfmisc_1(k2_zfmisc_1(C_2680,B_2681)))
      | ~ r1_tarski(k2_relat_1(D_2679),B_2681)
      | ~ m1_subset_1(D_2679,k1_zfmisc_1(k2_zfmisc_1(C_2680,A_2682))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_78528,plain,(
    ! [A_2850,B_2851] :
      ( m1_subset_1(A_2850,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2850),B_2851)))
      | ~ r1_tarski(k2_relat_1(A_2850),B_2851)
      | ~ v1_funct_1(A_2850)
      | ~ v1_relat_1(A_2850) ) ),
    inference(resolution,[status(thm)],[c_66,c_74725])).

tff(c_78578,plain,(
    ! [B_2851] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_2851)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_2851)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73507,c_78528])).

tff(c_78599,plain,(
    ! [B_2852] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_2852)))
      | ~ r1_tarski('#skF_3',B_2852) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74399,c_78578])).

tff(c_48,plain,(
    ! [C_38,A_36,B_37] :
      ( v1_funct_2(C_38,A_36,B_37)
      | ~ v1_partfun1(C_38,A_36)
      | ~ v1_funct_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_78615,plain,(
    ! [B_2852] :
      ( v1_funct_2('#skF_3','#skF_3',B_2852)
      | ~ v1_partfun1('#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski('#skF_3',B_2852) ) ),
    inference(resolution,[status(thm)],[c_78599,c_48])).

tff(c_78656,plain,(
    ! [B_2853] :
      ( v1_funct_2('#skF_3','#skF_3',B_2853)
      | ~ r1_tarski('#skF_3',B_2853) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_73836,c_78615])).

tff(c_73508,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73507,c_93])).

tff(c_78659,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_78656,c_73508])).

tff(c_78663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74441,c_78659])).

tff(c_78664,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_82557,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82532,c_78664])).

tff(c_82585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_82557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:30:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.68/11.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.68/12.01  
% 22.68/12.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.68/12.01  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 22.68/12.01  
% 22.68/12.01  %Foreground sorts:
% 22.68/12.01  
% 22.68/12.01  
% 22.68/12.01  %Background operators:
% 22.68/12.01  
% 22.68/12.01  
% 22.68/12.01  %Foreground operators:
% 22.68/12.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.68/12.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.68/12.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.68/12.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.68/12.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.68/12.01  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 22.68/12.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.68/12.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.68/12.01  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 22.68/12.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.68/12.01  tff('#skF_2', type, '#skF_2': $i).
% 22.68/12.01  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 22.68/12.01  tff('#skF_3', type, '#skF_3': $i).
% 22.68/12.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 22.68/12.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.68/12.01  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 22.68/12.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.68/12.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.68/12.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.68/12.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.68/12.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.68/12.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.68/12.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.68/12.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.68/12.01  
% 22.99/12.05  tff(f_166, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 22.99/12.05  tff(f_153, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 22.99/12.05  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 22.99/12.05  tff(f_100, axiom, (v1_relat_1(k1_wellord2(k1_xboole_0)) & v1_xboole_0(k1_wellord2(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_wellord2)).
% 22.99/12.05  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 22.99/12.05  tff(f_81, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 22.99/12.05  tff(f_50, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 22.99/12.05  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 22.99/12.05  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 22.99/12.05  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 22.99/12.05  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 22.99/12.05  tff(f_125, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 22.99/12.05  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 22.99/12.05  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 22.99/12.05  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 22.99/12.05  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 22.99/12.05  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (v1_relat_1(k1_wellord2(A)) & ~v1_xboole_0(k1_wellord2(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_wellord2)).
% 22.99/12.05  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 22.99/12.05  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 22.99/12.05  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 22.99/12.05  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 22.99/12.05  tff(c_74, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 22.99/12.05  tff(c_66, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_46), k2_relat_1(A_46)))) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.99/12.05  tff(c_79542, plain, (![D_2952, C_2953, B_2954, A_2955]: (m1_subset_1(D_2952, k1_zfmisc_1(k2_zfmisc_1(C_2953, B_2954))) | ~r1_tarski(k2_relat_1(D_2952), B_2954) | ~m1_subset_1(D_2952, k1_zfmisc_1(k2_zfmisc_1(C_2953, A_2955))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.99/12.05  tff(c_82532, plain, (![A_3109, B_3110]: (m1_subset_1(A_3109, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_3109), B_3110))) | ~r1_tarski(k2_relat_1(A_3109), B_3110) | ~v1_funct_1(A_3109) | ~v1_relat_1(A_3109))), inference(resolution, [status(thm)], [c_66, c_79542])).
% 22.99/12.05  tff(c_42, plain, (v1_relat_1(k1_wellord2(k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.99/12.05  tff(c_175, plain, (![A_66]: (k2_relat_1(A_66)!=k1_xboole_0 | k1_xboole_0=A_66 | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 22.99/12.05  tff(c_194, plain, (k2_relat_1(k1_wellord2(k1_xboole_0))!=k1_xboole_0 | k1_wellord2(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_175])).
% 22.99/12.05  tff(c_234, plain, (k2_relat_1(k1_wellord2(k1_xboole_0))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_194])).
% 22.99/12.05  tff(c_28, plain, (![A_18]: (k1_relat_1('#skF_1'(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.99/12.05  tff(c_32, plain, (![A_18]: (v1_relat_1('#skF_1'(A_18)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.99/12.05  tff(c_129, plain, (![A_64]: (k1_relat_1(A_64)!=k1_xboole_0 | k1_xboole_0=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_69])).
% 22.99/12.05  tff(c_138, plain, (![A_18]: (k1_relat_1('#skF_1'(A_18))!=k1_xboole_0 | '#skF_1'(A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_129])).
% 22.99/12.05  tff(c_152, plain, (![A_65]: (k1_xboole_0!=A_65 | '#skF_1'(A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_138])).
% 22.99/12.05  tff(c_162, plain, (![A_65]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_152, c_32])).
% 22.99/12.05  tff(c_196, plain, (![A_65]: (k1_xboole_0!=A_65)), inference(splitLeft, [status(thm)], [c_162])).
% 22.99/12.05  tff(c_102, plain, (![A_57, B_58]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_57, B_58)), B_58))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.99/12.05  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.99/12.05  tff(c_107, plain, (![A_57]: (k2_relat_1(k2_zfmisc_1(A_57, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_102, c_2])).
% 22.99/12.05  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_107])).
% 22.99/12.05  tff(c_203, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_162])).
% 22.99/12.05  tff(c_216, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_152, c_28])).
% 22.99/12.05  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 22.99/12.05  tff(c_414, plain, (![A_98, B_99]: (k2_relat_1(k2_zfmisc_1(A_98, B_99))!=k1_xboole_0 | k2_zfmisc_1(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_175])).
% 22.99/12.05  tff(c_418, plain, (![A_57]: (k2_zfmisc_1(A_57, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_414])).
% 22.99/12.05  tff(c_419, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_418, c_107])).
% 22.99/12.05  tff(c_148, plain, (![A_18]: (k1_xboole_0!=A_18 | '#skF_1'(A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_138])).
% 22.99/12.05  tff(c_30, plain, (![A_18]: (v1_funct_1('#skF_1'(A_18)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.99/12.05  tff(c_369, plain, (![A_90]: (m1_subset_1(A_90, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_90), k2_relat_1(A_90)))) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.99/12.05  tff(c_384, plain, (![A_18]: (m1_subset_1('#skF_1'(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, k2_relat_1('#skF_1'(A_18))))) | ~v1_funct_1('#skF_1'(A_18)) | ~v1_relat_1('#skF_1'(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_369])).
% 22.99/12.05  tff(c_574, plain, (![A_113]: (m1_subset_1('#skF_1'(A_113), k1_zfmisc_1(k2_zfmisc_1(A_113, k2_relat_1('#skF_1'(A_113))))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_384])).
% 22.99/12.05  tff(c_592, plain, (![A_18]: (m1_subset_1('#skF_1'(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, k2_relat_1(k1_xboole_0)))) | k1_xboole_0!=A_18)), inference(superposition, [status(thm), theory('equality')], [c_148, c_574])).
% 22.99/12.05  tff(c_604, plain, (![A_115]: (m1_subset_1('#skF_1'(A_115), k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0!=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_418, c_419, c_592])).
% 22.99/12.05  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.99/12.05  tff(c_617, plain, (![A_115]: (r1_tarski('#skF_1'(A_115), k1_xboole_0) | k1_xboole_0!=A_115)), inference(resolution, [status(thm)], [c_604, c_8])).
% 22.99/12.05  tff(c_521, plain, (![A_103, B_104]: (r1_tarski(k1_relat_1(A_103), k1_relat_1(B_104)) | ~r1_tarski(A_103, B_104) | ~v1_relat_1(B_104) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.99/12.05  tff(c_527, plain, (![A_18, B_104]: (r1_tarski(A_18, k1_relat_1(B_104)) | ~r1_tarski('#skF_1'(A_18), B_104) | ~v1_relat_1(B_104) | ~v1_relat_1('#skF_1'(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_521])).
% 22.99/12.05  tff(c_1103, plain, (![A_166, B_167]: (r1_tarski(A_166, k1_relat_1(B_167)) | ~r1_tarski('#skF_1'(A_166), B_167) | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_527])).
% 22.99/12.05  tff(c_1109, plain, (![A_115]: (r1_tarski(A_115, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_115)), inference(resolution, [status(thm)], [c_617, c_1103])).
% 22.99/12.05  tff(c_1136, plain, (![A_168]: (r1_tarski(A_168, k1_xboole_0) | k1_xboole_0!=A_168)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_216, c_1109])).
% 22.99/12.05  tff(c_493, plain, (![A_101, B_102]: (r1_tarski(k2_relat_1(A_101), k2_relat_1(B_102)) | ~r1_tarski(A_101, B_102) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.99/12.05  tff(c_502, plain, (![A_101]: (r1_tarski(k2_relat_1(A_101), k1_xboole_0) | ~r1_tarski(A_101, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_419, c_493])).
% 22.99/12.05  tff(c_862, plain, (![A_151]: (r1_tarski(k2_relat_1(A_151), k1_xboole_0) | ~r1_tarski(A_151, k1_xboole_0) | ~v1_relat_1(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_502])).
% 22.99/12.05  tff(c_875, plain, (![A_151]: (k2_relat_1(A_151)=k1_xboole_0 | ~r1_tarski(A_151, k1_xboole_0) | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_862, c_2])).
% 22.99/12.05  tff(c_1333, plain, (![A_181]: (k2_relat_1(A_181)=k1_xboole_0 | ~v1_relat_1(A_181) | k1_xboole_0!=A_181)), inference(resolution, [status(thm)], [c_1136, c_875])).
% 22.99/12.05  tff(c_1348, plain, (k2_relat_1(k1_wellord2(k1_xboole_0))=k1_xboole_0 | k1_wellord2(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_1333])).
% 22.99/12.05  tff(c_1359, plain, (k1_wellord2(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_234, c_1348])).
% 22.99/12.05  tff(c_40, plain, (v1_xboole_0(k1_wellord2(k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.99/12.05  tff(c_151, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_138])).
% 22.99/12.05  tff(c_530, plain, (![A_103, A_18]: (r1_tarski(k1_relat_1(A_103), A_18) | ~r1_tarski(A_103, '#skF_1'(A_18)) | ~v1_relat_1('#skF_1'(A_18)) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_28, c_521])).
% 22.99/12.05  tff(c_1269, plain, (![A_173, A_174]: (r1_tarski(k1_relat_1(A_173), A_174) | ~r1_tarski(A_173, '#skF_1'(A_174)) | ~v1_relat_1(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_530])).
% 22.99/12.05  tff(c_1287, plain, (![A_18, A_174]: (r1_tarski(A_18, A_174) | ~r1_tarski('#skF_1'(A_18), '#skF_1'(A_174)) | ~v1_relat_1('#skF_1'(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1269])).
% 22.99/12.05  tff(c_1556, plain, (![A_195, A_196]: (r1_tarski(A_195, A_196) | ~r1_tarski('#skF_1'(A_195), '#skF_1'(A_196)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1287])).
% 22.99/12.05  tff(c_2020, plain, (![A_212, A_213]: (r1_tarski(A_212, A_213) | ~r1_tarski('#skF_1'(A_212), k1_xboole_0) | k1_xboole_0!=A_213)), inference(superposition, [status(thm), theory('equality')], [c_148, c_1556])).
% 22.99/12.05  tff(c_2033, plain, (![A_115, A_213]: (r1_tarski(A_115, A_213) | k1_xboole_0!=A_213 | k1_xboole_0!=A_115)), inference(resolution, [status(thm)], [c_617, c_2020])).
% 22.99/12.05  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.99/12.05  tff(c_344, plain, (![C_86, A_87, B_88]: (v1_partfun1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_125])).
% 22.99/12.05  tff(c_349, plain, (![A_7, A_87, B_88]: (v1_partfun1(A_7, A_87) | ~v1_xboole_0(A_87) | ~r1_tarski(A_7, k2_zfmisc_1(A_87, B_88)))), inference(resolution, [status(thm)], [c_10, c_344])).
% 22.99/12.05  tff(c_7303, plain, (![A_427, A_428, B_429]: (v1_partfun1(k1_relat_1(A_427), A_428) | ~v1_xboole_0(A_428) | ~r1_tarski(A_427, '#skF_1'(k2_zfmisc_1(A_428, B_429))) | ~v1_relat_1(A_427))), inference(resolution, [status(thm)], [c_1269, c_349])).
% 22.99/12.05  tff(c_7326, plain, (![A_427, A_57]: (v1_partfun1(k1_relat_1(A_427), A_57) | ~v1_xboole_0(A_57) | ~r1_tarski(A_427, '#skF_1'(k1_xboole_0)) | ~v1_relat_1(A_427))), inference(superposition, [status(thm), theory('equality')], [c_418, c_7303])).
% 22.99/12.05  tff(c_7341, plain, (![A_430, A_431]: (v1_partfun1(k1_relat_1(A_430), A_431) | ~v1_xboole_0(A_431) | ~r1_tarski(A_430, k1_xboole_0) | ~v1_relat_1(A_430))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_7326])).
% 22.99/12.05  tff(c_7350, plain, (![A_18, A_431]: (v1_partfun1(A_18, A_431) | ~v1_xboole_0(A_431) | ~r1_tarski('#skF_1'(A_18), k1_xboole_0) | ~v1_relat_1('#skF_1'(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7341])).
% 22.99/12.05  tff(c_7357, plain, (![A_432, A_433]: (v1_partfun1(A_432, A_433) | ~v1_xboole_0(A_433) | ~r1_tarski('#skF_1'(A_432), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_7350])).
% 22.99/12.05  tff(c_7390, plain, (![A_432, A_433]: (v1_partfun1(A_432, A_433) | ~v1_xboole_0(A_433) | '#skF_1'(A_432)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2033, c_7357])).
% 22.99/12.05  tff(c_265, plain, (![A_75]: (k2_xboole_0(k1_relat_1(A_75), k2_relat_1(A_75))=k3_relat_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.99/12.05  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, k2_xboole_0(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.99/12.05  tff(c_291, plain, (![A_78]: (r1_tarski(k1_relat_1(A_78), k3_relat_1(A_78)) | ~v1_relat_1(A_78))), inference(superposition, [status(thm), theory('equality')], [c_265, c_4])).
% 22.99/12.05  tff(c_297, plain, (![A_18]: (r1_tarski(A_18, k3_relat_1('#skF_1'(A_18))) | ~v1_relat_1('#skF_1'(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_291])).
% 22.99/12.05  tff(c_301, plain, (![A_79]: (r1_tarski(A_79, k3_relat_1('#skF_1'(A_79))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_297])).
% 22.99/12.05  tff(c_324, plain, (r1_tarski(k1_xboole_0, k3_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_148, c_301])).
% 22.99/12.05  tff(c_160, plain, (![A_65]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_152, c_30])).
% 22.99/12.05  tff(c_168, plain, (![A_65]: (k1_xboole_0!=A_65)), inference(splitLeft, [status(thm)], [c_160])).
% 22.99/12.05  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_107])).
% 22.99/12.05  tff(c_174, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_160])).
% 22.99/12.05  tff(c_108, plain, (![A_59]: (k2_relat_1(k2_zfmisc_1(A_59, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_102, c_2])).
% 22.99/12.05  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_12, B_13)), B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.99/12.05  tff(c_113, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_16])).
% 22.99/12.05  tff(c_54, plain, (![A_43]: (v1_funct_2(k1_xboole_0, A_43, k1_xboole_0) | k1_xboole_0=A_43 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_43, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 22.99/12.05  tff(c_468, plain, (![A_43]: (v1_funct_2(k1_xboole_0, A_43, k1_xboole_0) | k1_xboole_0=A_43 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_54])).
% 22.99/12.05  tff(c_469, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_468])).
% 22.99/12.05  tff(c_473, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_469])).
% 22.99/12.05  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_473])).
% 22.99/12.05  tff(c_479, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_468])).
% 22.99/12.05  tff(c_797, plain, (![D_138, C_139, B_140, A_141]: (m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(C_139, B_140))) | ~r1_tarski(k2_relat_1(D_138), B_140) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(C_139, A_141))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.99/12.05  tff(c_11732, plain, (![D_543, A_544, B_545]: (m1_subset_1(D_543, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))) | ~r1_tarski(k2_relat_1(D_543), B_545) | ~m1_subset_1(D_543, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_418, c_797])).
% 22.99/12.05  tff(c_12126, plain, (![D_554, A_555, B_556]: (r1_tarski(D_554, k2_zfmisc_1(A_555, B_556)) | ~r1_tarski(k2_relat_1(D_554), B_556) | ~m1_subset_1(D_554, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_11732, c_8])).
% 22.99/12.05  tff(c_12208, plain, (![A_555, B_556]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_555, B_556)) | ~r1_tarski(k1_xboole_0, B_556) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_419, c_12126])).
% 22.99/12.05  tff(c_12257, plain, (![A_557, B_558]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_557, B_558)) | ~r1_tarski(k1_xboole_0, B_558))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_12208])).
% 22.99/12.05  tff(c_724, plain, (![C_128, A_129, B_130]: (v1_funct_2(C_128, A_129, B_130) | ~v1_partfun1(C_128, A_129) | ~v1_funct_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 22.99/12.05  tff(c_742, plain, (![A_7, A_129, B_130]: (v1_funct_2(A_7, A_129, B_130) | ~v1_partfun1(A_7, A_129) | ~v1_funct_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_129, B_130)))), inference(resolution, [status(thm)], [c_10, c_724])).
% 22.99/12.05  tff(c_12275, plain, (![A_557, B_558]: (v1_funct_2(k1_xboole_0, A_557, B_558) | ~v1_partfun1(k1_xboole_0, A_557) | ~v1_funct_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_558))), inference(resolution, [status(thm)], [c_12257, c_742])).
% 22.99/12.05  tff(c_12306, plain, (![A_557, B_558]: (v1_funct_2(k1_xboole_0, A_557, B_558) | ~v1_partfun1(k1_xboole_0, A_557) | ~r1_tarski(k1_xboole_0, B_558))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_12275])).
% 22.99/12.05  tff(c_96, plain, (![A_54]: (~v1_xboole_0(k1_wellord2(A_54)) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_108])).
% 22.99/12.05  tff(c_100, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_96])).
% 22.99/12.05  tff(c_239, plain, (![B_71, A_72]: (v1_xboole_0(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.99/12.05  tff(c_243, plain, (![A_7, B_8]: (v1_xboole_0(A_7) | ~v1_xboole_0(B_8) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_10, c_239])).
% 22.99/12.05  tff(c_1146, plain, (![A_168]: (v1_xboole_0(A_168) | ~v1_xboole_0(k1_xboole_0) | k1_xboole_0!=A_168)), inference(resolution, [status(thm)], [c_1136, c_243])).
% 22.99/12.05  tff(c_1160, plain, (![A_169]: (v1_xboole_0(A_169) | k1_xboole_0!=A_169)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1146])).
% 22.99/12.05  tff(c_320, plain, (![A_81]: (v1_xboole_0(A_81) | ~v1_xboole_0(k3_relat_1('#skF_1'(A_81))))), inference(resolution, [status(thm)], [c_301, c_243])).
% 22.99/12.05  tff(c_323, plain, (![A_18]: (v1_xboole_0(A_18) | ~v1_xboole_0(k3_relat_1(k1_xboole_0)) | k1_xboole_0!=A_18)), inference(superposition, [status(thm), theory('equality')], [c_148, c_320])).
% 22.99/12.05  tff(c_343, plain, (~v1_xboole_0(k3_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_323])).
% 22.99/12.05  tff(c_1184, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_1160, c_343])).
% 22.99/12.05  tff(c_307, plain, (![A_18]: (r1_tarski(A_18, k3_relat_1(k1_xboole_0)) | k1_xboole_0!=A_18)), inference(superposition, [status(thm), theory('equality')], [c_148, c_301])).
% 22.99/12.05  tff(c_404, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.99/12.05  tff(c_413, plain, (![A_95, B_96, A_7]: (k1_relset_1(A_95, B_96, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_95, B_96)))), inference(resolution, [status(thm)], [c_10, c_404])).
% 22.99/12.05  tff(c_12286, plain, (![A_557, B_558]: (k1_relset_1(A_557, B_558, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_558))), inference(resolution, [status(thm)], [c_12257, c_413])).
% 22.99/12.05  tff(c_12316, plain, (![A_559, B_560]: (k1_relset_1(A_559, B_560, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_560))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_12286])).
% 22.99/12.05  tff(c_12464, plain, (![A_559]: (k1_relset_1(A_559, k3_relat_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_307, c_12316])).
% 22.99/12.05  tff(c_280, plain, (![A_18]: (k2_xboole_0(A_18, k2_relat_1('#skF_1'(A_18)))=k3_relat_1('#skF_1'(A_18)) | ~v1_relat_1('#skF_1'(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_265])).
% 22.99/12.05  tff(c_350, plain, (![A_89]: (k2_xboole_0(A_89, k2_relat_1('#skF_1'(A_89)))=k3_relat_1('#skF_1'(A_89)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_280])).
% 22.99/12.05  tff(c_365, plain, (![A_18]: (k2_xboole_0(A_18, k2_relat_1(k1_xboole_0))=k3_relat_1('#skF_1'(A_18)) | k1_xboole_0!=A_18)), inference(superposition, [status(thm), theory('equality')], [c_148, c_350])).
% 22.99/12.05  tff(c_751, plain, (![A_132]: (k3_relat_1('#skF_1'(A_132))=k2_xboole_0(A_132, k1_xboole_0) | k1_xboole_0!=A_132)), inference(demodulation, [status(thm), theory('equality')], [c_419, c_365])).
% 22.99/12.05  tff(c_772, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=k3_relat_1(k1_xboole_0) | k1_xboole_0!=A_18 | k1_xboole_0!=A_18)), inference(superposition, [status(thm), theory('equality')], [c_148, c_751])).
% 22.99/12.05  tff(c_13234, plain, (![D_574, A_575, B_576]: (r1_tarski(D_574, k2_zfmisc_1(A_575, k2_xboole_0(k2_relat_1(D_574), B_576))) | ~m1_subset_1(D_574, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_12126])).
% 22.99/12.05  tff(c_13323, plain, (![A_575, B_576]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_575, k2_xboole_0(k1_xboole_0, B_576))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_419, c_13234])).
% 22.99/12.05  tff(c_13355, plain, (![A_577, B_578]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_577, k2_xboole_0(k1_xboole_0, B_578))))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_13323])).
% 22.99/12.05  tff(c_13431, plain, (![A_579]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_579, k3_relat_1(k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_772, c_13355])).
% 22.99/12.05  tff(c_1045, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 22.99/12.05  tff(c_1064, plain, (![B_159, A_160, A_7]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, A_7)=A_160 | ~v1_funct_2(A_7, A_160, B_159) | ~r1_tarski(A_7, k2_zfmisc_1(A_160, B_159)))), inference(resolution, [status(thm)], [c_10, c_1045])).
% 22.99/12.05  tff(c_13436, plain, (![A_579]: (k3_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relset_1(A_579, k3_relat_1(k1_xboole_0), k1_xboole_0)=A_579 | ~v1_funct_2(k1_xboole_0, A_579, k3_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_13431, c_1064])).
% 22.99/12.05  tff(c_13466, plain, (![A_579]: (k3_relat_1(k1_xboole_0)=k1_xboole_0 | k1_xboole_0=A_579 | ~v1_funct_2(k1_xboole_0, A_579, k3_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12464, c_13436])).
% 22.99/12.05  tff(c_13526, plain, (![A_582]: (k1_xboole_0=A_582 | ~v1_funct_2(k1_xboole_0, A_582, k3_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_1184, c_13466])).
% 22.99/12.05  tff(c_13530, plain, (![A_557]: (k1_xboole_0=A_557 | ~v1_partfun1(k1_xboole_0, A_557) | ~r1_tarski(k1_xboole_0, k3_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_12306, c_13526])).
% 22.99/12.05  tff(c_13558, plain, (![A_583]: (k1_xboole_0=A_583 | ~v1_partfun1(k1_xboole_0, A_583))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_13530])).
% 22.99/12.05  tff(c_13565, plain, (![A_433]: (k1_xboole_0=A_433 | ~v1_xboole_0(A_433) | '#skF_1'(k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7390, c_13558])).
% 22.99/12.05  tff(c_13610, plain, (![A_584]: (k1_xboole_0=A_584 | ~v1_xboole_0(A_584))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_13565])).
% 22.99/12.05  tff(c_13646, plain, (k1_wellord2(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_13610])).
% 22.99/12.05  tff(c_13661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1359, c_13646])).
% 22.99/12.05  tff(c_13672, plain, (![A_588]: (v1_xboole_0(A_588) | k1_xboole_0!=A_588)), inference(splitRight, [status(thm)], [c_323])).
% 22.99/12.05  tff(c_245, plain, (![A_73, B_74]: (v1_xboole_0(A_73) | ~v1_xboole_0(B_74) | ~r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_10, c_239])).
% 22.99/12.05  tff(c_263, plain, (v1_xboole_0(k2_relat_1('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_245])).
% 22.99/12.05  tff(c_264, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_263])).
% 22.99/12.05  tff(c_13687, plain, (k1_xboole_0!='#skF_2'), inference(resolution, [status(thm)], [c_13672, c_264])).
% 22.99/12.05  tff(c_14132, plain, (![D_639, C_640, B_641, A_642]: (m1_subset_1(D_639, k1_zfmisc_1(k2_zfmisc_1(C_640, B_641))) | ~r1_tarski(k2_relat_1(D_639), B_641) | ~m1_subset_1(D_639, k1_zfmisc_1(k2_zfmisc_1(C_640, A_642))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.99/12.05  tff(c_17197, plain, (![A_801, B_802]: (m1_subset_1(A_801, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_801), B_802))) | ~r1_tarski(k2_relat_1(A_801), B_802) | ~v1_funct_1(A_801) | ~v1_relat_1(A_801))), inference(resolution, [status(thm)], [c_66, c_14132])).
% 22.99/12.05  tff(c_34, plain, (![A_24, B_25, C_26]: (k1_relset_1(A_24, B_25, C_26)=k1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.99/12.05  tff(c_34333, plain, (![A_1287, B_1288]: (k1_relset_1(k1_relat_1(A_1287), B_1288, A_1287)=k1_relat_1(A_1287) | ~r1_tarski(k2_relat_1(A_1287), B_1288) | ~v1_funct_1(A_1287) | ~v1_relat_1(A_1287))), inference(resolution, [status(thm)], [c_17197, c_34])).
% 22.99/12.05  tff(c_34413, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_34333])).
% 22.99/12.05  tff(c_34453, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_34413])).
% 22.99/12.05  tff(c_60, plain, (![B_44, C_45, A_43]: (k1_xboole_0=B_44 | v1_funct_2(C_45, A_43, B_44) | k1_relset_1(A_43, B_44, C_45)!=A_43 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 22.99/12.05  tff(c_44092, plain, (![B_1574, A_1575]: (k1_xboole_0=B_1574 | v1_funct_2(A_1575, k1_relat_1(A_1575), B_1574) | k1_relset_1(k1_relat_1(A_1575), B_1574, A_1575)!=k1_relat_1(A_1575) | ~r1_tarski(k2_relat_1(A_1575), B_1574) | ~v1_funct_1(A_1575) | ~v1_relat_1(A_1575))), inference(resolution, [status(thm)], [c_17197, c_60])).
% 22.99/12.05  tff(c_72, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 22.99/12.05  tff(c_80, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72])).
% 22.99/12.05  tff(c_93, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_80])).
% 22.99/12.05  tff(c_44106, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44092, c_93])).
% 22.99/12.05  tff(c_44127, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_34453, c_44106])).
% 22.99/12.05  tff(c_44129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13687, c_44127])).
% 22.99/12.05  tff(c_44130, plain, (v1_xboole_0(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_263])).
% 22.99/12.05  tff(c_44247, plain, (![A_1594, B_1595]: (r1_tarski(k2_relat_1(A_1594), k2_relat_1(B_1595)) | ~r1_tarski(A_1594, B_1595) | ~v1_relat_1(B_1595) | ~v1_relat_1(A_1594))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.99/12.05  tff(c_49472, plain, (![A_1872, B_1873]: (v1_xboole_0(k2_relat_1(A_1872)) | ~v1_xboole_0(k2_relat_1(B_1873)) | ~r1_tarski(A_1872, B_1873) | ~v1_relat_1(B_1873) | ~v1_relat_1(A_1872))), inference(resolution, [status(thm)], [c_44247, c_243])).
% 22.99/12.05  tff(c_49499, plain, (![A_1872]: (v1_xboole_0(k2_relat_1(A_1872)) | ~r1_tarski(A_1872, '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_1872))), inference(resolution, [status(thm)], [c_44130, c_49472])).
% 22.99/12.05  tff(c_49522, plain, (![A_1874]: (v1_xboole_0(k2_relat_1(A_1874)) | ~r1_tarski(A_1874, '#skF_3') | ~v1_relat_1(A_1874))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_49499])).
% 22.99/12.05  tff(c_44257, plain, (![A_1594, B_1595]: (v1_xboole_0(k2_relat_1(A_1594)) | ~v1_xboole_0(k2_relat_1(B_1595)) | ~r1_tarski(A_1594, B_1595) | ~v1_relat_1(B_1595) | ~v1_relat_1(A_1594))), inference(resolution, [status(thm)], [c_44247, c_243])).
% 22.99/12.05  tff(c_49653, plain, (![A_1881, A_1882]: (v1_xboole_0(k2_relat_1(A_1881)) | ~r1_tarski(A_1881, A_1882) | ~v1_relat_1(A_1881) | ~r1_tarski(A_1882, '#skF_3') | ~v1_relat_1(A_1882))), inference(resolution, [status(thm)], [c_49522, c_44257])).
% 22.99/12.05  tff(c_49793, plain, (v1_xboole_0(k2_relat_1(k2_relat_1('#skF_3'))) | ~v1_relat_1(k2_relat_1('#skF_3')) | ~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_49653])).
% 22.99/12.05  tff(c_50141, plain, (~v1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_49793])).
% 22.99/12.05  tff(c_44847, plain, (![D_1651, C_1652, B_1653, A_1654]: (m1_subset_1(D_1651, k1_zfmisc_1(k2_zfmisc_1(C_1652, B_1653))) | ~r1_tarski(k2_relat_1(D_1651), B_1653) | ~m1_subset_1(D_1651, k1_zfmisc_1(k2_zfmisc_1(C_1652, A_1654))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.99/12.05  tff(c_48258, plain, (![A_1823, B_1824]: (m1_subset_1(A_1823, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1823), B_1824))) | ~r1_tarski(k2_relat_1(A_1823), B_1824) | ~v1_funct_1(A_1823) | ~v1_relat_1(A_1823))), inference(resolution, [status(thm)], [c_66, c_44847])).
% 22.99/12.05  tff(c_52884, plain, (![A_1980, B_1981]: (k1_relset_1(k1_relat_1(A_1980), B_1981, A_1980)=k1_relat_1(A_1980) | ~r1_tarski(k2_relat_1(A_1980), B_1981) | ~v1_funct_1(A_1980) | ~v1_relat_1(A_1980))), inference(resolution, [status(thm)], [c_48258, c_34])).
% 22.99/12.05  tff(c_52979, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_52884])).
% 22.99/12.05  tff(c_53024, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_52979])).
% 22.99/12.05  tff(c_61239, plain, (![B_2226, A_2227]: (k1_xboole_0=B_2226 | v1_funct_2(A_2227, k1_relat_1(A_2227), B_2226) | k1_relset_1(k1_relat_1(A_2227), B_2226, A_2227)!=k1_relat_1(A_2227) | ~r1_tarski(k2_relat_1(A_2227), B_2226) | ~v1_funct_1(A_2227) | ~v1_relat_1(A_2227))), inference(resolution, [status(thm)], [c_48258, c_60])).
% 22.99/12.05  tff(c_61245, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61239, c_93])).
% 22.99/12.05  tff(c_61259, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_53024, c_61245])).
% 22.99/12.05  tff(c_61559, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61259, c_203])).
% 22.99/12.05  tff(c_61568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50141, c_61559])).
% 22.99/12.05  tff(c_61570, plain, (v1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_49793])).
% 22.99/12.05  tff(c_44279, plain, (![A_1601, B_1602]: (k2_relat_1(k2_zfmisc_1(A_1601, B_1602))!=k1_xboole_0 | k2_zfmisc_1(A_1601, B_1602)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_175])).
% 22.99/12.05  tff(c_44283, plain, (![A_57]: (k2_zfmisc_1(A_57, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_44279])).
% 22.99/12.05  tff(c_44284, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44283, c_107])).
% 22.99/12.05  tff(c_44394, plain, (![A_1611]: (m1_subset_1(A_1611, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1611), k2_relat_1(A_1611)))) | ~v1_funct_1(A_1611) | ~v1_relat_1(A_1611))), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.99/12.05  tff(c_44412, plain, (![A_18]: (m1_subset_1('#skF_1'(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, k2_relat_1('#skF_1'(A_18))))) | ~v1_funct_1('#skF_1'(A_18)) | ~v1_relat_1('#skF_1'(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_44394])).
% 22.99/12.05  tff(c_44421, plain, (![A_1612]: (m1_subset_1('#skF_1'(A_1612), k1_zfmisc_1(k2_zfmisc_1(A_1612, k2_relat_1('#skF_1'(A_1612))))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_44412])).
% 22.99/12.05  tff(c_44439, plain, (![A_18]: (m1_subset_1('#skF_1'(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, k2_relat_1(k1_xboole_0)))) | k1_xboole_0!=A_18)), inference(superposition, [status(thm), theory('equality')], [c_148, c_44421])).
% 22.99/12.05  tff(c_44451, plain, (![A_1614]: (m1_subset_1('#skF_1'(A_1614), k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0!=A_1614)), inference(demodulation, [status(thm), theory('equality')], [c_44283, c_44284, c_44439])).
% 22.99/12.05  tff(c_44464, plain, (![A_1614]: (r1_tarski('#skF_1'(A_1614), k1_xboole_0) | k1_xboole_0!=A_1614)), inference(resolution, [status(thm)], [c_44451, c_8])).
% 22.99/12.05  tff(c_44264, plain, (![A_1599, B_1600]: (r1_tarski(k1_relat_1(A_1599), k1_relat_1(B_1600)) | ~r1_tarski(A_1599, B_1600) | ~v1_relat_1(B_1600) | ~v1_relat_1(A_1599))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.99/12.05  tff(c_44270, plain, (![A_18, B_1600]: (r1_tarski(A_18, k1_relat_1(B_1600)) | ~r1_tarski('#skF_1'(A_18), B_1600) | ~v1_relat_1(B_1600) | ~v1_relat_1('#skF_1'(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_44264])).
% 22.99/12.05  tff(c_44921, plain, (![A_1661, B_1662]: (r1_tarski(A_1661, k1_relat_1(B_1662)) | ~r1_tarski('#skF_1'(A_1661), B_1662) | ~v1_relat_1(B_1662))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44270])).
% 22.99/12.05  tff(c_44927, plain, (![A_1614]: (r1_tarski(A_1614, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_1614)), inference(resolution, [status(thm)], [c_44464, c_44921])).
% 22.99/12.05  tff(c_44948, plain, (![A_1614]: (r1_tarski(A_1614, k1_xboole_0) | k1_xboole_0!=A_1614)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_216, c_44927])).
% 22.99/12.05  tff(c_44273, plain, (![A_1599, A_18]: (r1_tarski(k1_relat_1(A_1599), A_18) | ~r1_tarski(A_1599, '#skF_1'(A_18)) | ~v1_relat_1('#skF_1'(A_18)) | ~v1_relat_1(A_1599))), inference(superposition, [status(thm), theory('equality')], [c_28, c_44264])).
% 22.99/12.05  tff(c_45105, plain, (![A_1673, A_1674]: (r1_tarski(k1_relat_1(A_1673), A_1674) | ~r1_tarski(A_1673, '#skF_1'(A_1674)) | ~v1_relat_1(A_1673))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44273])).
% 22.99/12.05  tff(c_45116, plain, (![A_1673]: (k1_relat_1(A_1673)=k1_xboole_0 | ~r1_tarski(A_1673, '#skF_1'(k1_xboole_0)) | ~v1_relat_1(A_1673))), inference(resolution, [status(thm)], [c_45105, c_2])).
% 22.99/12.05  tff(c_45435, plain, (![A_1696]: (k1_relat_1(A_1696)=k1_xboole_0 | ~r1_tarski(A_1696, k1_xboole_0) | ~v1_relat_1(A_1696))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_45116])).
% 22.99/12.05  tff(c_45459, plain, (![A_1614]: (k1_relat_1(A_1614)=k1_xboole_0 | ~v1_relat_1(A_1614) | k1_xboole_0!=A_1614)), inference(resolution, [status(thm)], [c_44948, c_45435])).
% 22.99/12.05  tff(c_61591, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k1_xboole_0!='#skF_2'), inference(resolution, [status(thm)], [c_61570, c_45459])).
% 22.99/12.05  tff(c_61595, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_61591])).
% 22.99/12.05  tff(c_63988, plain, (![A_2307, B_2308]: (k1_relset_1(k1_relat_1(A_2307), B_2308, A_2307)=k1_relat_1(A_2307) | ~r1_tarski(k2_relat_1(A_2307), B_2308) | ~v1_funct_1(A_2307) | ~v1_relat_1(A_2307))), inference(resolution, [status(thm)], [c_48258, c_34])).
% 22.99/12.05  tff(c_64080, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_63988])).
% 22.99/12.05  tff(c_64124, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64080])).
% 22.99/12.05  tff(c_72637, plain, (![B_2559, A_2560]: (k1_xboole_0=B_2559 | v1_funct_2(A_2560, k1_relat_1(A_2560), B_2559) | k1_relset_1(k1_relat_1(A_2560), B_2559, A_2560)!=k1_relat_1(A_2560) | ~r1_tarski(k2_relat_1(A_2560), B_2559) | ~v1_funct_1(A_2560) | ~v1_relat_1(A_2560))), inference(resolution, [status(thm)], [c_48258, c_60])).
% 22.99/12.05  tff(c_72643, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72637, c_93])).
% 22.99/12.05  tff(c_72657, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_64124, c_72643])).
% 22.99/12.05  tff(c_72659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61595, c_72657])).
% 22.99/12.05  tff(c_72661, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_61591])).
% 22.99/12.05  tff(c_195, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_78, c_175])).
% 22.99/12.05  tff(c_215, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_195])).
% 22.99/12.05  tff(c_72823, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72661, c_215])).
% 22.99/12.05  tff(c_73366, plain, (![A_2567]: (A_2567='#skF_2' | ~r1_tarski(A_2567, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72661, c_72661, c_2])).
% 22.99/12.05  tff(c_73380, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_74, c_73366])).
% 22.99/12.05  tff(c_73390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72823, c_73380])).
% 22.99/12.05  tff(c_73391, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_195])).
% 22.99/12.05  tff(c_158, plain, (![A_65]: (k1_relat_1(k1_xboole_0)=A_65 | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_152, c_28])).
% 22.99/12.05  tff(c_73483, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73391, c_73391, c_158])).
% 22.99/12.05  tff(c_150, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_78, c_129])).
% 22.99/12.05  tff(c_204, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_150])).
% 22.99/12.05  tff(c_73393, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73391, c_204])).
% 22.99/12.05  tff(c_73487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73483, c_73393])).
% 22.99/12.05  tff(c_73488, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_150])).
% 22.99/12.05  tff(c_73495, plain, (![A_57]: (k2_relat_1(k2_zfmisc_1(A_57, '#skF_3'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73488, c_73488, c_107])).
% 22.99/12.05  tff(c_192, plain, (![A_10, B_11]: (k2_relat_1(k2_zfmisc_1(A_10, B_11))!=k1_xboole_0 | k2_zfmisc_1(A_10, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_175])).
% 22.99/12.05  tff(c_74392, plain, (![A_2655, B_2656]: (k2_relat_1(k2_zfmisc_1(A_2655, B_2656))!='#skF_3' | k2_zfmisc_1(A_2655, B_2656)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73488, c_73488, c_192])).
% 22.99/12.05  tff(c_74396, plain, (![A_57]: (k2_zfmisc_1(A_57, '#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73495, c_74392])).
% 22.99/12.05  tff(c_74399, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74396, c_73495])).
% 22.99/12.05  tff(c_74441, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74399, c_74])).
% 22.99/12.05  tff(c_73496, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73488, c_100])).
% 22.99/12.05  tff(c_73489, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_150])).
% 22.99/12.05  tff(c_73507, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73488, c_73489])).
% 22.99/12.05  tff(c_73685, plain, (![A_2593]: (m1_subset_1(A_2593, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2593), k2_relat_1(A_2593)))) | ~v1_funct_1(A_2593) | ~v1_relat_1(A_2593))), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.99/12.05  tff(c_73700, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73507, c_73685])).
% 22.99/12.05  tff(c_73710, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_73700])).
% 22.99/12.05  tff(c_52, plain, (![C_42, A_39, B_40]: (v1_partfun1(C_42, A_39) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_125])).
% 22.99/12.05  tff(c_73827, plain, (v1_partfun1('#skF_3', '#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_73710, c_52])).
% 22.99/12.05  tff(c_73836, plain, (v1_partfun1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73496, c_73827])).
% 22.99/12.05  tff(c_74725, plain, (![D_2679, C_2680, B_2681, A_2682]: (m1_subset_1(D_2679, k1_zfmisc_1(k2_zfmisc_1(C_2680, B_2681))) | ~r1_tarski(k2_relat_1(D_2679), B_2681) | ~m1_subset_1(D_2679, k1_zfmisc_1(k2_zfmisc_1(C_2680, A_2682))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 22.99/12.05  tff(c_78528, plain, (![A_2850, B_2851]: (m1_subset_1(A_2850, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2850), B_2851))) | ~r1_tarski(k2_relat_1(A_2850), B_2851) | ~v1_funct_1(A_2850) | ~v1_relat_1(A_2850))), inference(resolution, [status(thm)], [c_66, c_74725])).
% 22.99/12.05  tff(c_78578, plain, (![B_2851]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_2851))) | ~r1_tarski(k2_relat_1('#skF_3'), B_2851) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_73507, c_78528])).
% 22.99/12.05  tff(c_78599, plain, (![B_2852]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_2852))) | ~r1_tarski('#skF_3', B_2852))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74399, c_78578])).
% 22.99/12.05  tff(c_48, plain, (![C_38, A_36, B_37]: (v1_funct_2(C_38, A_36, B_37) | ~v1_partfun1(C_38, A_36) | ~v1_funct_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 22.99/12.05  tff(c_78615, plain, (![B_2852]: (v1_funct_2('#skF_3', '#skF_3', B_2852) | ~v1_partfun1('#skF_3', '#skF_3') | ~v1_funct_1('#skF_3') | ~r1_tarski('#skF_3', B_2852))), inference(resolution, [status(thm)], [c_78599, c_48])).
% 22.99/12.05  tff(c_78656, plain, (![B_2853]: (v1_funct_2('#skF_3', '#skF_3', B_2853) | ~r1_tarski('#skF_3', B_2853))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_73836, c_78615])).
% 22.99/12.05  tff(c_73508, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_73507, c_93])).
% 22.99/12.05  tff(c_78659, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_78656, c_73508])).
% 22.99/12.05  tff(c_78663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74441, c_78659])).
% 22.99/12.05  tff(c_78664, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_80])).
% 22.99/12.05  tff(c_82557, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82532, c_78664])).
% 22.99/12.05  tff(c_82585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_82557])).
% 22.99/12.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.99/12.05  
% 22.99/12.05  Inference rules
% 22.99/12.05  ----------------------
% 22.99/12.05  #Ref     : 2
% 22.99/12.05  #Sup     : 17424
% 22.99/12.05  #Fact    : 0
% 22.99/12.05  #Define  : 0
% 22.99/12.05  #Split   : 73
% 22.99/12.05  #Chain   : 0
% 22.99/12.05  #Close   : 0
% 22.99/12.05  
% 22.99/12.05  Ordering : KBO
% 22.99/12.05  
% 22.99/12.05  Simplification rules
% 22.99/12.05  ----------------------
% 22.99/12.05  #Subsume      : 6675
% 22.99/12.05  #Demod        : 15719
% 22.99/12.05  #Tautology    : 5917
% 22.99/12.05  #SimpNegUnit  : 489
% 22.99/12.05  #BackRed      : 752
% 22.99/12.05  
% 22.99/12.05  #Partial instantiations: 0
% 22.99/12.05  #Strategies tried      : 1
% 22.99/12.05  
% 22.99/12.05  Timing (in seconds)
% 22.99/12.05  ----------------------
% 22.99/12.05  Preprocessing        : 0.44
% 22.99/12.05  Parsing              : 0.22
% 22.99/12.05  CNF conversion       : 0.03
% 22.99/12.05  Main loop            : 10.67
% 22.99/12.05  Inferencing          : 2.55
% 22.99/12.05  Reduction            : 4.02
% 22.99/12.05  Demodulation         : 2.91
% 22.99/12.05  BG Simplification    : 0.19
% 22.99/12.05  Subsumption          : 3.23
% 22.99/12.05  Abstraction          : 0.29
% 22.99/12.05  MUC search           : 0.00
% 22.99/12.05  Cooper               : 0.00
% 22.99/12.05  Total                : 11.19
% 22.99/12.05  Index Insertion      : 0.00
% 22.99/12.05  Index Deletion       : 0.00
% 22.99/12.05  Index Matching       : 0.00
% 22.99/12.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
