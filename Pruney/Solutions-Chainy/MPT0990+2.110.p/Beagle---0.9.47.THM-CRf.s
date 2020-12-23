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
% DateTime   : Thu Dec  3 10:13:12 EST 2020

% Result     : Theorem 9.99s
% Output     : CNFRefutation 9.99s
% Verified   : 
% Statistics : Number of formulae       :  169 (1610 expanded)
%              Number of leaves         :   52 ( 588 expanded)
%              Depth                    :   22
%              Number of atoms          :  377 (5513 expanded)
%              Number of equality atoms :  100 (1464 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_205,negated_conjecture,(
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

tff(f_157,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_169,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

tff(f_167,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_153,axiom,(
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

tff(c_70,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_117,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_82,c_117])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_126])).

tff(c_169,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_181,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_169])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_123,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_88,c_117])).

tff(c_132,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_180,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_169])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_28,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_367,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_376,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_367])).

tff(c_383,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_376])).

tff(c_242,plain,(
    ! [A_95] :
      ( k1_relat_1(k2_funct_1(A_95)) = k2_relat_1(A_95)
      | ~ v2_funct_1(A_95)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [B_72,A_73] :
      ( v4_relat_1(B_72,A_73)
      | ~ r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_167,plain,(
    ! [B_72] :
      ( v4_relat_1(B_72,k1_relat_1(B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_1500,plain,(
    ! [A_139] :
      ( v4_relat_1(k2_funct_1(A_139),k2_relat_1(A_139))
      | ~ v1_relat_1(k2_funct_1(A_139))
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_167])).

tff(c_1503,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_1500])).

tff(c_1508,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_76,c_1503])).

tff(c_1509,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1508])).

tff(c_1513,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1509])).

tff(c_1517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_1513])).

tff(c_1519,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1508])).

tff(c_58,plain,(
    ! [A_47] : m1_subset_1(k6_partfun1(A_47),k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_120,plain,(
    ! [A_47] :
      ( v1_relat_1(k6_partfun1(A_47))
      | ~ v1_relat_1(k2_zfmisc_1(A_47,A_47)) ) ),
    inference(resolution,[status(thm)],[c_58,c_117])).

tff(c_129,plain,(
    ! [A_47] : v1_relat_1(k6_partfun1(A_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_120])).

tff(c_62,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_40,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_relat_1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_93,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_partfun1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k5_relat_1(B_22,k6_relat_1(A_21)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_206,plain,(
    ! [B_86,A_87] :
      ( k5_relat_1(B_86,k6_partfun1(A_87)) = B_86
      | ~ r1_tarski(k2_relat_1(B_86),A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_24])).

tff(c_211,plain,(
    ! [B_86] :
      ( k5_relat_1(B_86,k6_partfun1(k2_relat_1(B_86))) = B_86
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_6,c_206])).

tff(c_397,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_211])).

tff(c_416,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_397])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = B_20
      | ~ r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_232,plain,(
    ! [A_93,B_94] :
      ( k5_relat_1(k6_partfun1(A_93),B_94) = B_94
      | ~ r1_tarski(k1_relat_1(B_94),A_93)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_22])).

tff(c_241,plain,(
    ! [B_94] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_94)),B_94) = B_94
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_232])).

tff(c_656,plain,(
    ! [A_118,B_119,C_120] :
      ( k5_relat_1(k5_relat_1(A_118,B_119),C_120) = k5_relat_1(A_118,k5_relat_1(B_119,C_120))
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_698,plain,(
    ! [B_94,C_120] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_94)),k5_relat_1(B_94,C_120)) = k5_relat_1(B_94,C_120)
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(B_94)))
      | ~ v1_relat_1(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_656])).

tff(c_1013,plain,(
    ! [B_128,C_129] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_128)),k5_relat_1(B_128,C_129)) = k5_relat_1(B_128,C_129)
      | ~ v1_relat_1(C_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_698])).

tff(c_1070,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_1013])).

tff(c_1111,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_129,c_416,c_1070])).

tff(c_717,plain,(
    ! [B_94,C_120] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_94)),k5_relat_1(B_94,C_120)) = k5_relat_1(B_94,C_120)
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_698])).

tff(c_1122,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))),'#skF_3') = k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_717])).

tff(c_1144,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_132,c_1111,c_1122])).

tff(c_20,plain,(
    ! [A_12,B_16,C_18] :
      ( k5_relat_1(k5_relat_1(A_12,B_16),C_18) = k5_relat_1(A_12,k5_relat_1(B_16,C_18))
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1215,plain,(
    ! [C_18] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))),k5_relat_1('#skF_3',C_18)) = k5_relat_1('#skF_3',C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1144,c_20])).

tff(c_1737,plain,(
    ! [C_148] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))),k5_relat_1('#skF_3',C_148)) = k5_relat_1('#skF_3',C_148)
      | ~ v1_relat_1(C_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_132,c_1215])).

tff(c_1788,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1737])).

tff(c_1822,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_76,c_1519,c_1788])).

tff(c_1848,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_241])).

tff(c_1871,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1848])).

tff(c_311,plain,(
    ! [A_99] :
      ( k2_relat_1(k2_funct_1(A_99)) = k1_relat_1(A_99)
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_95,plain,(
    ! [B_22,A_21] :
      ( k5_relat_1(B_22,k6_partfun1(A_21)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_24])).

tff(c_320,plain,(
    ! [A_99,A_21] :
      ( k5_relat_1(k2_funct_1(A_99),k6_partfun1(A_21)) = k2_funct_1(A_99)
      | ~ r1_tarski(k1_relat_1(A_99),A_21)
      | ~ v1_relat_1(k2_funct_1(A_99))
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_95])).

tff(c_5180,plain,(
    ! [A_230,C_231] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_230)),C_231) = k5_relat_1(A_230,k5_relat_1(k2_funct_1(A_230),C_231))
      | ~ v1_relat_1(C_231)
      | ~ v1_relat_1(k2_funct_1(A_230))
      | ~ v1_relat_1(A_230)
      | ~ v2_funct_1(A_230)
      | ~ v1_funct_1(A_230)
      | ~ v1_relat_1(A_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_656])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1944,plain,(
    ! [A_155,D_153,E_157,C_156,F_152,B_154] :
      ( k1_partfun1(A_155,B_154,C_156,D_153,E_157,F_152) = k5_relat_1(E_157,F_152)
      | ~ m1_subset_1(F_152,k1_zfmisc_1(k2_zfmisc_1(C_156,D_153)))
      | ~ v1_funct_1(F_152)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_1(E_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1954,plain,(
    ! [A_155,B_154,E_157] :
      ( k1_partfun1(A_155,B_154,'#skF_2','#skF_1',E_157,'#skF_4') = k5_relat_1(E_157,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_1(E_157) ) ),
    inference(resolution,[status(thm)],[c_82,c_1944])).

tff(c_2279,plain,(
    ! [A_173,B_174,E_175] :
      ( k1_partfun1(A_173,B_174,'#skF_2','#skF_1',E_175,'#skF_4') = k5_relat_1(E_175,'#skF_4')
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(E_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1954])).

tff(c_2297,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_2279])).

tff(c_2312,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2297])).

tff(c_52,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k1_partfun1(A_41,B_42,C_43,D_44,E_45,F_46),k1_zfmisc_1(k2_zfmisc_1(A_41,D_44)))
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_43,D_44)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2383,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2312,c_52])).

tff(c_2387,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_82,c_2383])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1446,plain,(
    ! [D_134,C_135,A_136,B_137] :
      ( D_134 = C_135
      | ~ r2_relset_1(A_136,B_137,C_135,D_134)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1458,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_1446])).

tff(c_1479,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1458])).

tff(c_2682,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_2312,c_2312,c_1479])).

tff(c_2706,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2682,c_717])).

tff(c_2717,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_135,c_2682,c_2706])).

tff(c_5217,plain,
    ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1')
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5180,c_2717])).

tff(c_5413,plain,(
    k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_76,c_132,c_1519,c_129,c_5217])).

tff(c_5618,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_5413])).

tff(c_5632,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_76,c_1519,c_1871,c_5618])).

tff(c_5635,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5632])).

tff(c_5958,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_5635])).

tff(c_5962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_180,c_5958])).

tff(c_5963,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5632])).

tff(c_18,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_406,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_18])).

tff(c_422,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_406])).

tff(c_574,plain,(
    ! [B_114,A_115] :
      ( k9_relat_1(B_114,k10_relat_1(B_114,A_115)) = A_115
      | ~ r1_tarski(A_115,k2_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_576,plain,(
    ! [A_115] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_115)) = A_115
      | ~ r1_tarski(A_115,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_574])).

tff(c_589,plain,(
    ! [A_116] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_116)) = A_116
      | ~ r1_tarski(A_116,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_576])).

tff(c_598,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_589])).

tff(c_606,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_598])).

tff(c_1163,plain,(
    ! [A_130,B_131] :
      ( k9_relat_1(k2_funct_1(A_130),k9_relat_1(A_130,B_131)) = B_131
      | ~ r1_tarski(B_131,k1_relat_1(A_130))
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1181,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_1163])).

tff(c_1191,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_76,c_6,c_1181])).

tff(c_16,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2455,plain,(
    ! [A_178] :
      ( k9_relat_1(k2_funct_1(A_178),k2_relat_1(A_178)) = k2_relat_1(k2_funct_1(A_178))
      | ~ v1_relat_1(k2_funct_1(A_178))
      | ~ v2_funct_1(A_178)
      | ~ v1_funct_1(A_178)
      | ~ v1_relat_1(A_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_16])).

tff(c_2473,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_2455])).

tff(c_2480,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_76,c_1519,c_1191,c_2473])).

tff(c_2519,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_211])).

tff(c_2560,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_2519])).

tff(c_5983,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5963,c_2560])).

tff(c_38,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_relat_1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_94,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_partfun1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_6394,plain,(
    ! [A_243,C_244] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_243)),C_244) = k5_relat_1(k2_funct_1(A_243),k5_relat_1(A_243,C_244))
      | ~ v1_relat_1(C_244)
      | ~ v1_relat_1(A_243)
      | ~ v1_relat_1(k2_funct_1(A_243))
      | ~ v2_funct_1(A_243)
      | ~ v1_funct_1(A_243)
      | ~ v1_relat_1(A_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_656])).

tff(c_6566,plain,(
    ! [C_244] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_244)) = k5_relat_1(k6_partfun1('#skF_2'),C_244)
      | ~ v1_relat_1(C_244)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_6394])).

tff(c_9432,plain,(
    ! [C_301] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_301)) = k5_relat_1(k6_partfun1('#skF_2'),C_301)
      | ~ v1_relat_1(C_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_92,c_76,c_1519,c_132,c_6566])).

tff(c_9495,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2682,c_9432])).

tff(c_9568,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_5983,c_9495])).

tff(c_240,plain,(
    ! [A_6,B_7] :
      ( k5_relat_1(k6_partfun1(A_6),B_7) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_232])).

tff(c_9614,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9568,c_240])).

tff(c_9637,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_181,c_9614])).

tff(c_9639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_9637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.99/3.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.53  
% 9.99/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.53  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.99/3.53  
% 9.99/3.53  %Foreground sorts:
% 9.99/3.53  
% 9.99/3.53  
% 9.99/3.53  %Background operators:
% 9.99/3.53  
% 9.99/3.53  
% 9.99/3.53  %Foreground operators:
% 9.99/3.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.99/3.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.99/3.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.99/3.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.99/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.99/3.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.99/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.99/3.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.99/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.99/3.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.99/3.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.99/3.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.99/3.53  tff('#skF_2', type, '#skF_2': $i).
% 9.99/3.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.99/3.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.99/3.53  tff('#skF_3', type, '#skF_3': $i).
% 9.99/3.53  tff('#skF_1', type, '#skF_1': $i).
% 9.99/3.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.99/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.99/3.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.99/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.99/3.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.99/3.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.99/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.99/3.53  tff('#skF_4', type, '#skF_4': $i).
% 9.99/3.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.99/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.99/3.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.99/3.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.99/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.99/3.53  
% 9.99/3.56  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.99/3.56  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.99/3.56  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.99/3.56  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.99/3.56  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.99/3.56  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.99/3.56  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.99/3.56  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.99/3.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.99/3.56  tff(f_157, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.99/3.56  tff(f_169, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.99/3.56  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.99/3.56  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 9.99/3.56  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 9.99/3.56  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.99/3.56  tff(f_167, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.99/3.56  tff(f_153, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.99/3.56  tff(f_141, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.99/3.56  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 9.99/3.56  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 9.99/3.56  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 9.99/3.56  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 9.99/3.56  tff(c_70, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.99/3.56  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.99/3.56  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.99/3.56  tff(c_117, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.99/3.56  tff(c_126, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_82, c_117])).
% 9.99/3.56  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_126])).
% 9.99/3.56  tff(c_169, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.99/3.56  tff(c_181, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_169])).
% 9.99/3.56  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.99/3.56  tff(c_123, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_88, c_117])).
% 9.99/3.56  tff(c_132, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_123])).
% 9.99/3.56  tff(c_180, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_88, c_169])).
% 9.99/3.56  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.99/3.56  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.99/3.56  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.99/3.56  tff(c_28, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.99/3.56  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.99/3.56  tff(c_367, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.99/3.56  tff(c_376, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_367])).
% 9.99/3.56  tff(c_383, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_376])).
% 9.99/3.56  tff(c_242, plain, (![A_95]: (k1_relat_1(k2_funct_1(A_95))=k2_relat_1(A_95) | ~v2_funct_1(A_95) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.99/3.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.99/3.56  tff(c_162, plain, (![B_72, A_73]: (v4_relat_1(B_72, A_73) | ~r1_tarski(k1_relat_1(B_72), A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.99/3.56  tff(c_167, plain, (![B_72]: (v4_relat_1(B_72, k1_relat_1(B_72)) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_6, c_162])).
% 9.99/3.56  tff(c_1500, plain, (![A_139]: (v4_relat_1(k2_funct_1(A_139), k2_relat_1(A_139)) | ~v1_relat_1(k2_funct_1(A_139)) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(superposition, [status(thm), theory('equality')], [c_242, c_167])).
% 9.99/3.56  tff(c_1503, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_383, c_1500])).
% 9.99/3.56  tff(c_1508, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_76, c_1503])).
% 9.99/3.56  tff(c_1509, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1508])).
% 9.99/3.56  tff(c_1513, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1509])).
% 9.99/3.56  tff(c_1517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_1513])).
% 9.99/3.56  tff(c_1519, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1508])).
% 9.99/3.56  tff(c_58, plain, (![A_47]: (m1_subset_1(k6_partfun1(A_47), k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.99/3.56  tff(c_120, plain, (![A_47]: (v1_relat_1(k6_partfun1(A_47)) | ~v1_relat_1(k2_zfmisc_1(A_47, A_47)))), inference(resolution, [status(thm)], [c_58, c_117])).
% 9.99/3.56  tff(c_129, plain, (![A_47]: (v1_relat_1(k6_partfun1(A_47)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_120])).
% 9.99/3.56  tff(c_62, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.99/3.56  tff(c_40, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_relat_1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.99/3.56  tff(c_93, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_partfun1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40])).
% 9.99/3.56  tff(c_24, plain, (![B_22, A_21]: (k5_relat_1(B_22, k6_relat_1(A_21))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.99/3.56  tff(c_206, plain, (![B_86, A_87]: (k5_relat_1(B_86, k6_partfun1(A_87))=B_86 | ~r1_tarski(k2_relat_1(B_86), A_87) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_24])).
% 9.99/3.56  tff(c_211, plain, (![B_86]: (k5_relat_1(B_86, k6_partfun1(k2_relat_1(B_86)))=B_86 | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_6, c_206])).
% 9.99/3.56  tff(c_397, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_383, c_211])).
% 9.99/3.56  tff(c_416, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_397])).
% 9.99/3.56  tff(c_22, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=B_20 | ~r1_tarski(k1_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.99/3.56  tff(c_232, plain, (![A_93, B_94]: (k5_relat_1(k6_partfun1(A_93), B_94)=B_94 | ~r1_tarski(k1_relat_1(B_94), A_93) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_22])).
% 9.99/3.56  tff(c_241, plain, (![B_94]: (k5_relat_1(k6_partfun1(k1_relat_1(B_94)), B_94)=B_94 | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_6, c_232])).
% 9.99/3.56  tff(c_656, plain, (![A_118, B_119, C_120]: (k5_relat_1(k5_relat_1(A_118, B_119), C_120)=k5_relat_1(A_118, k5_relat_1(B_119, C_120)) | ~v1_relat_1(C_120) | ~v1_relat_1(B_119) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.99/3.56  tff(c_698, plain, (![B_94, C_120]: (k5_relat_1(k6_partfun1(k1_relat_1(B_94)), k5_relat_1(B_94, C_120))=k5_relat_1(B_94, C_120) | ~v1_relat_1(C_120) | ~v1_relat_1(B_94) | ~v1_relat_1(k6_partfun1(k1_relat_1(B_94))) | ~v1_relat_1(B_94))), inference(superposition, [status(thm), theory('equality')], [c_241, c_656])).
% 9.99/3.56  tff(c_1013, plain, (![B_128, C_129]: (k5_relat_1(k6_partfun1(k1_relat_1(B_128)), k5_relat_1(B_128, C_129))=k5_relat_1(B_128, C_129) | ~v1_relat_1(C_129) | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_698])).
% 9.99/3.56  tff(c_1070, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_416, c_1013])).
% 9.99/3.56  tff(c_1111, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_129, c_416, c_1070])).
% 9.99/3.56  tff(c_717, plain, (![B_94, C_120]: (k5_relat_1(k6_partfun1(k1_relat_1(B_94)), k5_relat_1(B_94, C_120))=k5_relat_1(B_94, C_120) | ~v1_relat_1(C_120) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_698])).
% 9.99/3.56  tff(c_1122, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), '#skF_3')=k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1111, c_717])).
% 9.99/3.56  tff(c_1144, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_132, c_1111, c_1122])).
% 9.99/3.56  tff(c_20, plain, (![A_12, B_16, C_18]: (k5_relat_1(k5_relat_1(A_12, B_16), C_18)=k5_relat_1(A_12, k5_relat_1(B_16, C_18)) | ~v1_relat_1(C_18) | ~v1_relat_1(B_16) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.99/3.56  tff(c_1215, plain, (![C_18]: (k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), k5_relat_1('#skF_3', C_18))=k5_relat_1('#skF_3', C_18) | ~v1_relat_1(C_18) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))))), inference(superposition, [status(thm), theory('equality')], [c_1144, c_20])).
% 9.99/3.56  tff(c_1737, plain, (![C_148]: (k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), k5_relat_1('#skF_3', C_148))=k5_relat_1('#skF_3', C_148) | ~v1_relat_1(C_148))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_132, c_1215])).
% 9.99/3.56  tff(c_1788, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_93, c_1737])).
% 9.99/3.56  tff(c_1822, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_76, c_1519, c_1788])).
% 9.99/3.56  tff(c_1848, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1822, c_241])).
% 9.99/3.56  tff(c_1871, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_1848])).
% 9.99/3.56  tff(c_311, plain, (![A_99]: (k2_relat_1(k2_funct_1(A_99))=k1_relat_1(A_99) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.99/3.56  tff(c_95, plain, (![B_22, A_21]: (k5_relat_1(B_22, k6_partfun1(A_21))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_24])).
% 9.99/3.56  tff(c_320, plain, (![A_99, A_21]: (k5_relat_1(k2_funct_1(A_99), k6_partfun1(A_21))=k2_funct_1(A_99) | ~r1_tarski(k1_relat_1(A_99), A_21) | ~v1_relat_1(k2_funct_1(A_99)) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_311, c_95])).
% 9.99/3.56  tff(c_5180, plain, (![A_230, C_231]: (k5_relat_1(k6_partfun1(k1_relat_1(A_230)), C_231)=k5_relat_1(A_230, k5_relat_1(k2_funct_1(A_230), C_231)) | ~v1_relat_1(C_231) | ~v1_relat_1(k2_funct_1(A_230)) | ~v1_relat_1(A_230) | ~v2_funct_1(A_230) | ~v1_funct_1(A_230) | ~v1_relat_1(A_230))), inference(superposition, [status(thm), theory('equality')], [c_93, c_656])).
% 9.99/3.56  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.99/3.56  tff(c_1944, plain, (![A_155, D_153, E_157, C_156, F_152, B_154]: (k1_partfun1(A_155, B_154, C_156, D_153, E_157, F_152)=k5_relat_1(E_157, F_152) | ~m1_subset_1(F_152, k1_zfmisc_1(k2_zfmisc_1(C_156, D_153))) | ~v1_funct_1(F_152) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_1(E_157))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.99/3.56  tff(c_1954, plain, (![A_155, B_154, E_157]: (k1_partfun1(A_155, B_154, '#skF_2', '#skF_1', E_157, '#skF_4')=k5_relat_1(E_157, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_1(E_157))), inference(resolution, [status(thm)], [c_82, c_1944])).
% 9.99/3.56  tff(c_2279, plain, (![A_173, B_174, E_175]: (k1_partfun1(A_173, B_174, '#skF_2', '#skF_1', E_175, '#skF_4')=k5_relat_1(E_175, '#skF_4') | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(E_175))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1954])).
% 9.99/3.56  tff(c_2297, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_2279])).
% 9.99/3.56  tff(c_2312, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2297])).
% 9.99/3.56  tff(c_52, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (m1_subset_1(k1_partfun1(A_41, B_42, C_43, D_44, E_45, F_46), k1_zfmisc_1(k2_zfmisc_1(A_41, D_44))) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_43, D_44))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.99/3.56  tff(c_2383, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2312, c_52])).
% 9.99/3.56  tff(c_2387, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_82, c_2383])).
% 9.99/3.56  tff(c_78, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.99/3.56  tff(c_1446, plain, (![D_134, C_135, A_136, B_137]: (D_134=C_135 | ~r2_relset_1(A_136, B_137, C_135, D_134) | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.99/3.56  tff(c_1458, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_78, c_1446])).
% 9.99/3.56  tff(c_1479, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1458])).
% 9.99/3.56  tff(c_2682, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_2312, c_2312, c_1479])).
% 9.99/3.56  tff(c_2706, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2682, c_717])).
% 9.99/3.56  tff(c_2717, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_135, c_2682, c_2706])).
% 9.99/3.56  tff(c_5217, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1') | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5180, c_2717])).
% 9.99/3.56  tff(c_5413, plain, (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_76, c_132, c_1519, c_129, c_5217])).
% 9.99/3.56  tff(c_5618, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_320, c_5413])).
% 9.99/3.56  tff(c_5632, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_76, c_1519, c_1871, c_5618])).
% 9.99/3.56  tff(c_5635, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_5632])).
% 9.99/3.56  tff(c_5958, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_5635])).
% 9.99/3.56  tff(c_5962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_180, c_5958])).
% 9.99/3.56  tff(c_5963, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5632])).
% 9.99/3.56  tff(c_18, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.99/3.56  tff(c_406, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_383, c_18])).
% 9.99/3.56  tff(c_422, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_406])).
% 9.99/3.56  tff(c_574, plain, (![B_114, A_115]: (k9_relat_1(B_114, k10_relat_1(B_114, A_115))=A_115 | ~r1_tarski(A_115, k2_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.99/3.56  tff(c_576, plain, (![A_115]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_115))=A_115 | ~r1_tarski(A_115, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_383, c_574])).
% 9.99/3.56  tff(c_589, plain, (![A_116]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_116))=A_116 | ~r1_tarski(A_116, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_576])).
% 9.99/3.56  tff(c_598, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_422, c_589])).
% 9.99/3.56  tff(c_606, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_598])).
% 9.99/3.56  tff(c_1163, plain, (![A_130, B_131]: (k9_relat_1(k2_funct_1(A_130), k9_relat_1(A_130, B_131))=B_131 | ~r1_tarski(B_131, k1_relat_1(A_130)) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.99/3.56  tff(c_1181, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_606, c_1163])).
% 9.99/3.56  tff(c_1191, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_76, c_6, c_1181])).
% 9.99/3.56  tff(c_16, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.99/3.56  tff(c_2455, plain, (![A_178]: (k9_relat_1(k2_funct_1(A_178), k2_relat_1(A_178))=k2_relat_1(k2_funct_1(A_178)) | ~v1_relat_1(k2_funct_1(A_178)) | ~v2_funct_1(A_178) | ~v1_funct_1(A_178) | ~v1_relat_1(A_178))), inference(superposition, [status(thm), theory('equality')], [c_242, c_16])).
% 9.99/3.56  tff(c_2473, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_383, c_2455])).
% 9.99/3.56  tff(c_2480, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_76, c_1519, c_1191, c_2473])).
% 9.99/3.56  tff(c_2519, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2480, c_211])).
% 9.99/3.56  tff(c_2560, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1519, c_2519])).
% 9.99/3.56  tff(c_5983, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5963, c_2560])).
% 9.99/3.56  tff(c_38, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_relat_1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.99/3.56  tff(c_94, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_partfun1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 9.99/3.56  tff(c_6394, plain, (![A_243, C_244]: (k5_relat_1(k6_partfun1(k2_relat_1(A_243)), C_244)=k5_relat_1(k2_funct_1(A_243), k5_relat_1(A_243, C_244)) | ~v1_relat_1(C_244) | ~v1_relat_1(A_243) | ~v1_relat_1(k2_funct_1(A_243)) | ~v2_funct_1(A_243) | ~v1_funct_1(A_243) | ~v1_relat_1(A_243))), inference(superposition, [status(thm), theory('equality')], [c_94, c_656])).
% 9.99/3.56  tff(c_6566, plain, (![C_244]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_244))=k5_relat_1(k6_partfun1('#skF_2'), C_244) | ~v1_relat_1(C_244) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_383, c_6394])).
% 9.99/3.56  tff(c_9432, plain, (![C_301]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_301))=k5_relat_1(k6_partfun1('#skF_2'), C_301) | ~v1_relat_1(C_301))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_92, c_76, c_1519, c_132, c_6566])).
% 9.99/3.56  tff(c_9495, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2682, c_9432])).
% 9.99/3.56  tff(c_9568, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_5983, c_9495])).
% 9.99/3.56  tff(c_240, plain, (![A_6, B_7]: (k5_relat_1(k6_partfun1(A_6), B_7)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_232])).
% 9.99/3.56  tff(c_9614, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9568, c_240])).
% 9.99/3.56  tff(c_9637, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_181, c_9614])).
% 9.99/3.56  tff(c_9639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_9637])).
% 9.99/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.56  
% 9.99/3.56  Inference rules
% 9.99/3.56  ----------------------
% 9.99/3.56  #Ref     : 0
% 9.99/3.56  #Sup     : 2022
% 9.99/3.56  #Fact    : 0
% 9.99/3.56  #Define  : 0
% 9.99/3.56  #Split   : 9
% 9.99/3.56  #Chain   : 0
% 9.99/3.56  #Close   : 0
% 9.99/3.56  
% 9.99/3.56  Ordering : KBO
% 9.99/3.56  
% 9.99/3.56  Simplification rules
% 9.99/3.56  ----------------------
% 9.99/3.56  #Subsume      : 52
% 9.99/3.56  #Demod        : 3232
% 9.99/3.56  #Tautology    : 764
% 9.99/3.56  #SimpNegUnit  : 2
% 9.99/3.56  #BackRed      : 49
% 9.99/3.56  
% 9.99/3.56  #Partial instantiations: 0
% 9.99/3.56  #Strategies tried      : 1
% 9.99/3.56  
% 9.99/3.56  Timing (in seconds)
% 9.99/3.56  ----------------------
% 9.99/3.56  Preprocessing        : 0.40
% 9.99/3.57  Parsing              : 0.23
% 9.99/3.57  CNF conversion       : 0.03
% 9.99/3.57  Main loop            : 2.33
% 9.99/3.57  Inferencing          : 0.64
% 9.99/3.57  Reduction            : 1.12
% 9.99/3.57  Demodulation         : 0.93
% 9.99/3.57  BG Simplification    : 0.07
% 9.99/3.57  Subsumption          : 0.38
% 9.99/3.57  Abstraction          : 0.09
% 9.99/3.57  MUC search           : 0.00
% 9.99/3.57  Cooper               : 0.00
% 9.99/3.57  Total                : 2.78
% 9.99/3.57  Index Insertion      : 0.00
% 9.99/3.57  Index Deletion       : 0.00
% 9.99/3.57  Index Matching       : 0.00
% 9.99/3.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
