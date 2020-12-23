%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:13 EST 2020

% Result     : Theorem 9.41s
% Output     : CNFRefutation 9.62s
% Verified   : 
% Statistics : Number of formulae       :  169 (1608 expanded)
%              Number of leaves         :   51 ( 580 expanded)
%              Depth                    :   25
%              Number of atoms          :  366 (4884 expanded)
%              Number of equality atoms :   98 (1308 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_203,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_167,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_143,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_155,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_165,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_68,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_124,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_124])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_160,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_172,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_160])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_130,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_124])).

tff(c_139,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_130])).

tff(c_171,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_160])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_28,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_78,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_330,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_336,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_330])).

tff(c_342,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_336])).

tff(c_204,plain,(
    ! [A_85] :
      ( k1_relat_1(k2_funct_1(A_85)) = k2_relat_1(A_85)
      | ~ v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [B_81,A_82] :
      ( v4_relat_1(B_81,A_82)
      | ~ r1_tarski(k1_relat_1(B_81),A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_201,plain,(
    ! [B_81] :
      ( v4_relat_1(B_81,k1_relat_1(B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_192])).

tff(c_653,plain,(
    ! [A_117] :
      ( v4_relat_1(k2_funct_1(A_117),k2_relat_1(A_117))
      | ~ v1_relat_1(k2_funct_1(A_117))
      | ~ v2_funct_1(A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_201])).

tff(c_656,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_653])).

tff(c_661,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_74,c_656])).

tff(c_728,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_661])).

tff(c_731,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_728])).

tff(c_735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_731])).

tff(c_737,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_661])).

tff(c_60,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_52,plain,(
    ! [A_41] : m1_subset_1(k6_relat_1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_91,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_127,plain,(
    ! [A_41] :
      ( v1_relat_1(k6_partfun1(A_41))
      | ~ v1_relat_1(k2_zfmisc_1(A_41,A_41)) ) ),
    inference(resolution,[status(thm)],[c_91,c_124])).

tff(c_136,plain,(
    ! [A_41] : v1_relat_1(k6_partfun1(A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_127])).

tff(c_170,plain,(
    ! [A_41] : v4_relat_1(k6_partfun1(A_41),A_41) ),
    inference(resolution,[status(thm)],[c_91,c_160])).

tff(c_40,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_relat_1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_92,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_partfun1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k5_relat_1(B_22,k6_relat_1(A_21)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_279,plain,(
    ! [B_94,A_95] :
      ( k5_relat_1(B_94,k6_partfun1(A_95)) = B_94
      | ~ r1_tarski(k2_relat_1(B_94),A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24])).

tff(c_287,plain,(
    ! [B_94] :
      ( k5_relat_1(B_94,k6_partfun1(k2_relat_1(B_94))) = B_94
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_279])).

tff(c_351,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_287])).

tff(c_364,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_351])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = B_20
      | ~ r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_254,plain,(
    ! [A_91,B_92] :
      ( k5_relat_1(k6_partfun1(A_91),B_92) = B_92
      | ~ r1_tarski(k1_relat_1(B_92),A_91)
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_266,plain,(
    ! [B_92] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_92)),B_92) = B_92
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_662,plain,(
    ! [A_118,B_119,C_120] :
      ( k5_relat_1(k5_relat_1(A_118,B_119),C_120) = k5_relat_1(A_118,k5_relat_1(B_119,C_120))
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_711,plain,(
    ! [B_92,C_120] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_92)),k5_relat_1(B_92,C_120)) = k5_relat_1(B_92,C_120)
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(B_92)))
      | ~ v1_relat_1(B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_662])).

tff(c_834,plain,(
    ! [B_123,C_124] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_123)),k5_relat_1(B_123,C_124)) = k5_relat_1(B_123,C_124)
      | ~ v1_relat_1(C_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_711])).

tff(c_879,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_834])).

tff(c_915,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_136,c_364,c_879])).

tff(c_20,plain,(
    ! [A_12,B_16,C_18] :
      ( k5_relat_1(k5_relat_1(A_12,B_16),C_18) = k5_relat_1(A_12,k5_relat_1(B_16,C_18))
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_962,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_18)) = k5_relat_1('#skF_3',C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_20])).

tff(c_1103,plain,(
    ! [C_128] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_128)) = k5_relat_1('#skF_3',C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_139,c_962])).

tff(c_1141,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1103])).

tff(c_1173,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_74,c_737,c_1141])).

tff(c_265,plain,(
    ! [A_6,B_7] :
      ( k5_relat_1(k6_partfun1(A_6),B_7) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_254])).

tff(c_1224,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_265])).

tff(c_1235,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_170,c_1224])).

tff(c_34,plain,(
    ! [A_29] :
      ( k2_relat_1(k2_funct_1(A_29)) = k1_relat_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3109,plain,(
    ! [A_206,A_207] :
      ( k5_relat_1(k2_funct_1(A_206),k6_partfun1(A_207)) = k2_funct_1(A_206)
      | ~ r1_tarski(k1_relat_1(A_206),A_207)
      | ~ v1_relat_1(k2_funct_1(A_206))
      | ~ v2_funct_1(A_206)
      | ~ v1_funct_1(A_206)
      | ~ v1_relat_1(A_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_279])).

tff(c_1249,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),C_18) = k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_18))
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_20])).

tff(c_1263,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),C_18) = k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_18))
      | ~ v1_relat_1(C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_737,c_1249])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1681,plain,(
    ! [D_155,F_158,C_159,B_156,A_157,E_154] :
      ( m1_subset_1(k1_partfun1(A_157,B_156,C_159,D_155,E_154,F_158),k1_zfmisc_1(k2_zfmisc_1(A_157,D_155)))
      | ~ m1_subset_1(F_158,k1_zfmisc_1(k2_zfmisc_1(C_159,D_155)))
      | ~ v1_funct_1(F_158)
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156)))
      | ~ v1_funct_1(E_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_76,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1181,plain,(
    ! [D_129,C_130,A_131,B_132] :
      ( D_129 = C_130
      | ~ r2_relset_1(A_131,B_132,C_130,D_129)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1193,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_76,c_1181])).

tff(c_1214,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1193])).

tff(c_1272,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1214])).

tff(c_1694,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1681,c_1272])).

tff(c_1716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_1694])).

tff(c_1717,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1214])).

tff(c_2083,plain,(
    ! [A_174,D_172,E_176,B_173,C_175,F_171] :
      ( k1_partfun1(A_174,B_173,C_175,D_172,E_176,F_171) = k5_relat_1(E_176,F_171)
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(C_175,D_172)))
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173)))
      | ~ v1_funct_1(E_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2093,plain,(
    ! [A_174,B_173,E_176] :
      ( k1_partfun1(A_174,B_173,'#skF_2','#skF_1',E_176,'#skF_4') = k5_relat_1(E_176,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173)))
      | ~ v1_funct_1(E_176) ) ),
    inference(resolution,[status(thm)],[c_80,c_2083])).

tff(c_2320,plain,(
    ! [A_193,B_194,E_195] :
      ( k1_partfun1(A_193,B_194,'#skF_2','#skF_1',E_195,'#skF_4') = k5_relat_1(E_195,'#skF_4')
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2093])).

tff(c_2338,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_2320])).

tff(c_2353,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1717,c_2338])).

tff(c_727,plain,(
    ! [B_92,C_120] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_92)),k5_relat_1(B_92,C_120)) = k5_relat_1(B_92,C_120)
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_711])).

tff(c_2363,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_727])).

tff(c_2372,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_142,c_2353,c_2363])).

tff(c_2553,plain,
    ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1')
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1263,c_2372])).

tff(c_2569,plain,(
    k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2553])).

tff(c_3115,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3109,c_2569])).

tff(c_3152,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_74,c_737,c_1235,c_3115])).

tff(c_3172,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3152])).

tff(c_3175,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_3172])).

tff(c_3179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_171,c_3175])).

tff(c_3180,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3152])).

tff(c_18,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_360,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_18])).

tff(c_370,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_360])).

tff(c_571,plain,(
    ! [B_113,A_114] :
      ( k9_relat_1(B_113,k10_relat_1(B_113,A_114)) = A_114
      | ~ r1_tarski(A_114,k2_relat_1(B_113))
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_573,plain,(
    ! [A_114] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_114)) = A_114
      | ~ r1_tarski(A_114,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_571])).

tff(c_586,plain,(
    ! [A_115] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_115)) = A_115
      | ~ r1_tarski(A_115,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_573])).

tff(c_595,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_586])).

tff(c_603,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_595])).

tff(c_923,plain,(
    ! [A_125,B_126] :
      ( k9_relat_1(k2_funct_1(A_125),k9_relat_1(A_125,B_126)) = B_126
      | ~ r1_tarski(B_126,k1_relat_1(A_125))
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_941,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_923])).

tff(c_951,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_74,c_6,c_941])).

tff(c_16,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2431,plain,(
    ! [A_196] :
      ( k9_relat_1(k2_funct_1(A_196),k2_relat_1(A_196)) = k2_relat_1(k2_funct_1(A_196))
      | ~ v1_relat_1(k2_funct_1(A_196))
      | ~ v2_funct_1(A_196)
      | ~ v1_funct_1(A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_16])).

tff(c_2449,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_2431])).

tff(c_2456,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_74,c_737,c_951,c_2449])).

tff(c_2486,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2456,c_287])).

tff(c_2523,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_2486])).

tff(c_3202,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3180,c_2523])).

tff(c_38,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_relat_1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_93,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_partfun1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38])).

tff(c_5230,plain,(
    ! [A_248,C_249] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_248)),C_249) = k5_relat_1(k2_funct_1(A_248),k5_relat_1(A_248,C_249))
      | ~ v1_relat_1(C_249)
      | ~ v1_relat_1(A_248)
      | ~ v1_relat_1(k2_funct_1(A_248))
      | ~ v2_funct_1(A_248)
      | ~ v1_funct_1(A_248)
      | ~ v1_relat_1(A_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_662])).

tff(c_5363,plain,(
    ! [C_249] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_249)) = k5_relat_1(k6_partfun1('#skF_2'),C_249)
      | ~ v1_relat_1(C_249)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_5230])).

tff(c_8542,plain,(
    ! [C_314] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_314)) = k5_relat_1(k6_partfun1('#skF_2'),C_314)
      | ~ v1_relat_1(C_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_74,c_737,c_139,c_5363])).

tff(c_8605,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_8542])).

tff(c_8666,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_3202,c_8605])).

tff(c_8789,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8666,c_265])).

tff(c_8810,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_172,c_8789])).

tff(c_8812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:27:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.41/3.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.31  
% 9.41/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.32  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.41/3.32  
% 9.41/3.32  %Foreground sorts:
% 9.41/3.32  
% 9.41/3.32  
% 9.41/3.32  %Background operators:
% 9.41/3.32  
% 9.41/3.32  
% 9.41/3.32  %Foreground operators:
% 9.41/3.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.41/3.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.41/3.32  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.41/3.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.41/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.41/3.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.41/3.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.41/3.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.41/3.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.41/3.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.41/3.32  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.41/3.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.41/3.32  tff('#skF_2', type, '#skF_2': $i).
% 9.41/3.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.41/3.32  tff('#skF_3', type, '#skF_3': $i).
% 9.41/3.32  tff('#skF_1', type, '#skF_1': $i).
% 9.41/3.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.41/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.41/3.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.41/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.41/3.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.41/3.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.41/3.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.41/3.32  tff('#skF_4', type, '#skF_4': $i).
% 9.41/3.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.41/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.41/3.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.41/3.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.41/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.41/3.32  
% 9.62/3.34  tff(f_203, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.62/3.34  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.62/3.34  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.62/3.34  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.62/3.34  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.62/3.34  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.62/3.34  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.62/3.34  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.62/3.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.62/3.34  tff(f_167, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.62/3.34  tff(f_143, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.62/3.34  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.62/3.34  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 9.62/3.34  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 9.62/3.34  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.62/3.34  tff(f_155, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.62/3.34  tff(f_141, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.62/3.34  tff(f_165, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.62/3.34  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 9.62/3.34  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 9.62/3.34  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 9.62/3.34  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 9.62/3.34  tff(c_68, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.62/3.34  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.62/3.34  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.62/3.34  tff(c_124, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.62/3.34  tff(c_133, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_124])).
% 9.62/3.34  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_133])).
% 9.62/3.34  tff(c_160, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.62/3.34  tff(c_172, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_160])).
% 9.62/3.34  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.62/3.34  tff(c_130, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_124])).
% 9.62/3.34  tff(c_139, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_130])).
% 9.62/3.34  tff(c_171, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_160])).
% 9.62/3.34  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.62/3.34  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.62/3.34  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.62/3.34  tff(c_28, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.62/3.34  tff(c_78, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.62/3.34  tff(c_330, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.62/3.34  tff(c_336, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_330])).
% 9.62/3.34  tff(c_342, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_336])).
% 9.62/3.34  tff(c_204, plain, (![A_85]: (k1_relat_1(k2_funct_1(A_85))=k2_relat_1(A_85) | ~v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.62/3.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.62/3.34  tff(c_192, plain, (![B_81, A_82]: (v4_relat_1(B_81, A_82) | ~r1_tarski(k1_relat_1(B_81), A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.62/3.34  tff(c_201, plain, (![B_81]: (v4_relat_1(B_81, k1_relat_1(B_81)) | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_6, c_192])).
% 9.62/3.34  tff(c_653, plain, (![A_117]: (v4_relat_1(k2_funct_1(A_117), k2_relat_1(A_117)) | ~v1_relat_1(k2_funct_1(A_117)) | ~v2_funct_1(A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_204, c_201])).
% 9.62/3.34  tff(c_656, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_342, c_653])).
% 9.62/3.34  tff(c_661, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_74, c_656])).
% 9.62/3.34  tff(c_728, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_661])).
% 9.62/3.34  tff(c_731, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_728])).
% 9.62/3.34  tff(c_735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_731])).
% 9.62/3.34  tff(c_737, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_661])).
% 9.62/3.34  tff(c_60, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.62/3.34  tff(c_52, plain, (![A_41]: (m1_subset_1(k6_relat_1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.62/3.34  tff(c_91, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 9.62/3.34  tff(c_127, plain, (![A_41]: (v1_relat_1(k6_partfun1(A_41)) | ~v1_relat_1(k2_zfmisc_1(A_41, A_41)))), inference(resolution, [status(thm)], [c_91, c_124])).
% 9.62/3.34  tff(c_136, plain, (![A_41]: (v1_relat_1(k6_partfun1(A_41)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_127])).
% 9.62/3.34  tff(c_170, plain, (![A_41]: (v4_relat_1(k6_partfun1(A_41), A_41))), inference(resolution, [status(thm)], [c_91, c_160])).
% 9.62/3.34  tff(c_40, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_relat_1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.62/3.34  tff(c_92, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_partfun1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40])).
% 9.62/3.34  tff(c_24, plain, (![B_22, A_21]: (k5_relat_1(B_22, k6_relat_1(A_21))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.62/3.34  tff(c_279, plain, (![B_94, A_95]: (k5_relat_1(B_94, k6_partfun1(A_95))=B_94 | ~r1_tarski(k2_relat_1(B_94), A_95) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24])).
% 9.62/3.34  tff(c_287, plain, (![B_94]: (k5_relat_1(B_94, k6_partfun1(k2_relat_1(B_94)))=B_94 | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_6, c_279])).
% 9.62/3.34  tff(c_351, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_342, c_287])).
% 9.62/3.34  tff(c_364, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_351])).
% 9.62/3.34  tff(c_22, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=B_20 | ~r1_tarski(k1_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.62/3.34  tff(c_254, plain, (![A_91, B_92]: (k5_relat_1(k6_partfun1(A_91), B_92)=B_92 | ~r1_tarski(k1_relat_1(B_92), A_91) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22])).
% 9.62/3.34  tff(c_266, plain, (![B_92]: (k5_relat_1(k6_partfun1(k1_relat_1(B_92)), B_92)=B_92 | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_6, c_254])).
% 9.62/3.34  tff(c_662, plain, (![A_118, B_119, C_120]: (k5_relat_1(k5_relat_1(A_118, B_119), C_120)=k5_relat_1(A_118, k5_relat_1(B_119, C_120)) | ~v1_relat_1(C_120) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.62/3.34  tff(c_711, plain, (![B_92, C_120]: (k5_relat_1(k6_partfun1(k1_relat_1(B_92)), k5_relat_1(B_92, C_120))=k5_relat_1(B_92, C_120) | ~v1_relat_1(C_120) | ~v1_relat_1(B_92) | ~v1_relat_1(k6_partfun1(k1_relat_1(B_92))) | ~v1_relat_1(B_92))), inference(superposition, [status(thm), theory('equality')], [c_266, c_662])).
% 9.62/3.34  tff(c_834, plain, (![B_123, C_124]: (k5_relat_1(k6_partfun1(k1_relat_1(B_123)), k5_relat_1(B_123, C_124))=k5_relat_1(B_123, C_124) | ~v1_relat_1(C_124) | ~v1_relat_1(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_711])).
% 9.62/3.34  tff(c_879, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_364, c_834])).
% 9.62/3.34  tff(c_915, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_136, c_364, c_879])).
% 9.62/3.34  tff(c_20, plain, (![A_12, B_16, C_18]: (k5_relat_1(k5_relat_1(A_12, B_16), C_18)=k5_relat_1(A_12, k5_relat_1(B_16, C_18)) | ~v1_relat_1(C_18) | ~v1_relat_1(B_16) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.62/3.34  tff(c_962, plain, (![C_18]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_18))=k5_relat_1('#skF_3', C_18) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_915, c_20])).
% 9.62/3.34  tff(c_1103, plain, (![C_128]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_128))=k5_relat_1('#skF_3', C_128) | ~v1_relat_1(C_128))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_139, c_962])).
% 9.62/3.34  tff(c_1141, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_1103])).
% 9.62/3.34  tff(c_1173, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_74, c_737, c_1141])).
% 9.62/3.34  tff(c_265, plain, (![A_6, B_7]: (k5_relat_1(k6_partfun1(A_6), B_7)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_254])).
% 9.62/3.34  tff(c_1224, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1173, c_265])).
% 9.62/3.34  tff(c_1235, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_170, c_1224])).
% 9.62/3.34  tff(c_34, plain, (![A_29]: (k2_relat_1(k2_funct_1(A_29))=k1_relat_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.62/3.34  tff(c_3109, plain, (![A_206, A_207]: (k5_relat_1(k2_funct_1(A_206), k6_partfun1(A_207))=k2_funct_1(A_206) | ~r1_tarski(k1_relat_1(A_206), A_207) | ~v1_relat_1(k2_funct_1(A_206)) | ~v2_funct_1(A_206) | ~v1_funct_1(A_206) | ~v1_relat_1(A_206))), inference(superposition, [status(thm), theory('equality')], [c_34, c_279])).
% 9.62/3.34  tff(c_1249, plain, (![C_18]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), C_18)=k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_18)) | ~v1_relat_1(C_18) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_20])).
% 9.62/3.34  tff(c_1263, plain, (![C_18]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), C_18)=k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_18)) | ~v1_relat_1(C_18))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_737, c_1249])).
% 9.62/3.34  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.62/3.34  tff(c_1681, plain, (![D_155, F_158, C_159, B_156, A_157, E_154]: (m1_subset_1(k1_partfun1(A_157, B_156, C_159, D_155, E_154, F_158), k1_zfmisc_1(k2_zfmisc_1(A_157, D_155))) | ~m1_subset_1(F_158, k1_zfmisc_1(k2_zfmisc_1(C_159, D_155))) | ~v1_funct_1(F_158) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))) | ~v1_funct_1(E_154))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.62/3.34  tff(c_76, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 9.62/3.34  tff(c_1181, plain, (![D_129, C_130, A_131, B_132]: (D_129=C_130 | ~r2_relset_1(A_131, B_132, C_130, D_129) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.62/3.34  tff(c_1193, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_76, c_1181])).
% 9.62/3.34  tff(c_1214, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1193])).
% 9.62/3.34  tff(c_1272, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1214])).
% 9.62/3.34  tff(c_1694, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1681, c_1272])).
% 9.62/3.34  tff(c_1716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_1694])).
% 9.62/3.34  tff(c_1717, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1214])).
% 9.62/3.34  tff(c_2083, plain, (![A_174, D_172, E_176, B_173, C_175, F_171]: (k1_partfun1(A_174, B_173, C_175, D_172, E_176, F_171)=k5_relat_1(E_176, F_171) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(C_175, D_172))) | ~v1_funct_1(F_171) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))) | ~v1_funct_1(E_176))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.62/3.34  tff(c_2093, plain, (![A_174, B_173, E_176]: (k1_partfun1(A_174, B_173, '#skF_2', '#skF_1', E_176, '#skF_4')=k5_relat_1(E_176, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))) | ~v1_funct_1(E_176))), inference(resolution, [status(thm)], [c_80, c_2083])).
% 9.62/3.34  tff(c_2320, plain, (![A_193, B_194, E_195]: (k1_partfun1(A_193, B_194, '#skF_2', '#skF_1', E_195, '#skF_4')=k5_relat_1(E_195, '#skF_4') | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_funct_1(E_195))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2093])).
% 9.62/3.34  tff(c_2338, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_2320])).
% 9.62/3.34  tff(c_2353, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1717, c_2338])).
% 9.62/3.34  tff(c_727, plain, (![B_92, C_120]: (k5_relat_1(k6_partfun1(k1_relat_1(B_92)), k5_relat_1(B_92, C_120))=k5_relat_1(B_92, C_120) | ~v1_relat_1(C_120) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_711])).
% 9.62/3.34  tff(c_2363, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2353, c_727])).
% 9.62/3.34  tff(c_2372, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_142, c_2353, c_2363])).
% 9.62/3.34  tff(c_2553, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1') | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1263, c_2372])).
% 9.62/3.34  tff(c_2569, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2553])).
% 9.62/3.34  tff(c_3115, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3109, c_2569])).
% 9.62/3.34  tff(c_3152, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_74, c_737, c_1235, c_3115])).
% 9.62/3.34  tff(c_3172, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3152])).
% 9.62/3.34  tff(c_3175, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_3172])).
% 9.62/3.34  tff(c_3179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_171, c_3175])).
% 9.62/3.34  tff(c_3180, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3152])).
% 9.62/3.34  tff(c_18, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.62/3.34  tff(c_360, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_342, c_18])).
% 9.62/3.34  tff(c_370, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_360])).
% 9.62/3.34  tff(c_571, plain, (![B_113, A_114]: (k9_relat_1(B_113, k10_relat_1(B_113, A_114))=A_114 | ~r1_tarski(A_114, k2_relat_1(B_113)) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.62/3.34  tff(c_573, plain, (![A_114]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_114))=A_114 | ~r1_tarski(A_114, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_571])).
% 9.62/3.34  tff(c_586, plain, (![A_115]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_115))=A_115 | ~r1_tarski(A_115, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_573])).
% 9.62/3.34  tff(c_595, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_370, c_586])).
% 9.62/3.34  tff(c_603, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_595])).
% 9.62/3.34  tff(c_923, plain, (![A_125, B_126]: (k9_relat_1(k2_funct_1(A_125), k9_relat_1(A_125, B_126))=B_126 | ~r1_tarski(B_126, k1_relat_1(A_125)) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.62/3.34  tff(c_941, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_603, c_923])).
% 9.62/3.34  tff(c_951, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_74, c_6, c_941])).
% 9.62/3.34  tff(c_16, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.62/3.34  tff(c_2431, plain, (![A_196]: (k9_relat_1(k2_funct_1(A_196), k2_relat_1(A_196))=k2_relat_1(k2_funct_1(A_196)) | ~v1_relat_1(k2_funct_1(A_196)) | ~v2_funct_1(A_196) | ~v1_funct_1(A_196) | ~v1_relat_1(A_196))), inference(superposition, [status(thm), theory('equality')], [c_204, c_16])).
% 9.62/3.34  tff(c_2449, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_342, c_2431])).
% 9.62/3.34  tff(c_2456, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_74, c_737, c_951, c_2449])).
% 9.62/3.34  tff(c_2486, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2456, c_287])).
% 9.62/3.34  tff(c_2523, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_2486])).
% 9.62/3.34  tff(c_3202, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3180, c_2523])).
% 9.62/3.34  tff(c_38, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_relat_1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.62/3.34  tff(c_93, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_partfun1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 9.62/3.34  tff(c_5230, plain, (![A_248, C_249]: (k5_relat_1(k6_partfun1(k2_relat_1(A_248)), C_249)=k5_relat_1(k2_funct_1(A_248), k5_relat_1(A_248, C_249)) | ~v1_relat_1(C_249) | ~v1_relat_1(A_248) | ~v1_relat_1(k2_funct_1(A_248)) | ~v2_funct_1(A_248) | ~v1_funct_1(A_248) | ~v1_relat_1(A_248))), inference(superposition, [status(thm), theory('equality')], [c_93, c_662])).
% 9.62/3.34  tff(c_5363, plain, (![C_249]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_249))=k5_relat_1(k6_partfun1('#skF_2'), C_249) | ~v1_relat_1(C_249) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_5230])).
% 9.62/3.34  tff(c_8542, plain, (![C_314]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_314))=k5_relat_1(k6_partfun1('#skF_2'), C_314) | ~v1_relat_1(C_314))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_74, c_737, c_139, c_5363])).
% 9.62/3.34  tff(c_8605, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2353, c_8542])).
% 9.62/3.34  tff(c_8666, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_3202, c_8605])).
% 9.62/3.34  tff(c_8789, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8666, c_265])).
% 9.62/3.34  tff(c_8810, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_172, c_8789])).
% 9.62/3.34  tff(c_8812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_8810])).
% 9.62/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.62/3.34  
% 9.62/3.34  Inference rules
% 9.62/3.34  ----------------------
% 9.62/3.34  #Ref     : 0
% 9.62/3.34  #Sup     : 1868
% 9.62/3.34  #Fact    : 0
% 9.62/3.34  #Define  : 0
% 9.62/3.34  #Split   : 9
% 9.62/3.34  #Chain   : 0
% 9.62/3.34  #Close   : 0
% 9.62/3.34  
% 9.62/3.34  Ordering : KBO
% 9.62/3.34  
% 9.62/3.34  Simplification rules
% 9.62/3.34  ----------------------
% 9.62/3.34  #Subsume      : 49
% 9.62/3.34  #Demod        : 2871
% 9.62/3.34  #Tautology    : 701
% 9.62/3.34  #SimpNegUnit  : 1
% 9.62/3.34  #BackRed      : 32
% 9.62/3.34  
% 9.62/3.34  #Partial instantiations: 0
% 9.62/3.34  #Strategies tried      : 1
% 9.62/3.34  
% 9.62/3.34  Timing (in seconds)
% 9.62/3.34  ----------------------
% 9.62/3.34  Preprocessing        : 0.40
% 9.62/3.34  Parsing              : 0.22
% 9.62/3.34  CNF conversion       : 0.03
% 9.62/3.34  Main loop            : 2.12
% 9.62/3.34  Inferencing          : 0.58
% 9.62/3.34  Reduction            : 1.01
% 9.62/3.34  Demodulation         : 0.82
% 9.62/3.34  BG Simplification    : 0.07
% 9.62/3.34  Subsumption          : 0.35
% 9.62/3.34  Abstraction          : 0.08
% 9.62/3.34  MUC search           : 0.00
% 9.62/3.34  Cooper               : 0.00
% 9.62/3.34  Total                : 2.57
% 9.62/3.34  Index Insertion      : 0.00
% 9.62/3.34  Index Deletion       : 0.00
% 9.62/3.34  Index Matching       : 0.00
% 9.62/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
