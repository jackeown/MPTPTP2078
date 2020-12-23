%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:55 EST 2020

% Result     : Theorem 8.27s
% Output     : CNFRefutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 307 expanded)
%              Number of leaves         :   47 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1083 expanded)
%              Number of equality atoms :   59 ( 298 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_172,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_146,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_134,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_144,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_126,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_138,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_126])).

tff(c_203,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_216,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_203])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_137,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_126])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_26,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_359,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_relset_1(A_95,B_96,C_97) = k2_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_365,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_359])).

tff(c_372,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_365])).

tff(c_301,plain,(
    ! [A_88] :
      ( k1_relat_1(k2_funct_1(A_88)) = k2_relat_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [B_70,A_71] :
      ( v4_relat_1(B_70,A_71)
      | ~ r1_tarski(k1_relat_1(B_70),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194,plain,(
    ! [B_70] :
      ( v4_relat_1(B_70,k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_184])).

tff(c_1739,plain,(
    ! [A_160] :
      ( v4_relat_1(k2_funct_1(A_160),k2_relat_1(A_160))
      | ~ v1_relat_1(k2_funct_1(A_160))
      | ~ v2_funct_1(A_160)
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_194])).

tff(c_1742,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_1739])).

tff(c_1750,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82,c_66,c_1742])).

tff(c_1753,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1750])).

tff(c_1756,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1753])).

tff(c_1760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82,c_1756])).

tff(c_1762,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1750])).

tff(c_215,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_203])).

tff(c_58,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_16,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1694,plain,(
    ! [B_159,D_158,A_154,F_155,E_157,C_156] :
      ( m1_subset_1(k1_partfun1(A_154,B_159,C_156,D_158,E_157,F_155),k1_zfmisc_1(k2_zfmisc_1(A_154,D_158)))
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(C_156,D_158)))
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_154,B_159)))
      | ~ v1_funct_1(E_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_875,plain,(
    ! [D_118,C_119,A_120,B_121] :
      ( D_118 = C_119
      | ~ r2_relset_1(A_120,B_121,C_119,D_118)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_883,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_875])).

tff(c_898,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_883])).

tff(c_1081,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_898])).

tff(c_1707,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1694,c_1081])).

tff(c_1729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_1707])).

tff(c_1730,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_898])).

tff(c_2238,plain,(
    ! [D_177,B_178,C_181,F_180,E_176,A_179] :
      ( k1_partfun1(A_179,B_178,C_181,D_177,E_176,F_180) = k5_relat_1(E_176,F_180)
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(C_181,D_177)))
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178)))
      | ~ v1_funct_1(E_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2244,plain,(
    ! [A_179,B_178,E_176] :
      ( k1_partfun1(A_179,B_178,'#skF_2','#skF_1',E_176,'#skF_4') = k5_relat_1(E_176,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178)))
      | ~ v1_funct_1(E_176) ) ),
    inference(resolution,[status(thm)],[c_72,c_2238])).

tff(c_2607,plain,(
    ! [A_195,B_196,E_197] :
      ( k1_partfun1(A_195,B_196,'#skF_2','#skF_1',E_197,'#skF_4') = k5_relat_1(E_197,'#skF_4')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ v1_funct_1(E_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2244])).

tff(c_2616,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2607])).

tff(c_2624,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1730,c_2616])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_5,B_7)),k1_relat_1(A_5))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2649,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2624,c_12])).

tff(c_2665,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_138,c_88,c_2649])).

tff(c_217,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k1_relat_1(B_79),A_80)
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,(
    ! [B_79,A_80] :
      ( k1_relat_1(B_79) = A_80
      | ~ r1_tarski(A_80,k1_relat_1(B_79))
      | ~ v4_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_217,c_2])).

tff(c_2669,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2665,c_227])).

tff(c_2674,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_215,c_2669])).

tff(c_289,plain,(
    ! [A_87] :
      ( k2_relat_1(k2_funct_1(A_87)) = k1_relat_1(A_87)
      | ~ v2_funct_1(A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_partfun1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_2747,plain,(
    ! [A_198] :
      ( k5_relat_1(k2_funct_1(A_198),k6_partfun1(k1_relat_1(A_198))) = k2_funct_1(A_198)
      | ~ v1_relat_1(k2_funct_1(A_198))
      | ~ v2_funct_1(A_198)
      | ~ v1_funct_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_85])).

tff(c_2768,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2674,c_2747])).

tff(c_2786,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82,c_66,c_1762,c_2768])).

tff(c_32,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_relat_1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_752,plain,(
    ! [A_113] :
      ( k5_relat_1(k2_funct_1(A_113),A_113) = k6_partfun1(k2_relat_1(A_113))
      | ~ v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_14,plain,(
    ! [A_8,B_12,C_14] :
      ( k5_relat_1(k5_relat_1(A_8,B_12),C_14) = k5_relat_1(A_8,k5_relat_1(B_12,C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6508,plain,(
    ! [A_266,C_267] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_266)),C_267) = k5_relat_1(k2_funct_1(A_266),k5_relat_1(A_266,C_267))
      | ~ v1_relat_1(C_267)
      | ~ v1_relat_1(A_266)
      | ~ v1_relat_1(k2_funct_1(A_266))
      | ~ v2_funct_1(A_266)
      | ~ v1_funct_1(A_266)
      | ~ v1_relat_1(A_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_14])).

tff(c_6767,plain,(
    ! [C_267] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_267)) = k5_relat_1(k6_partfun1('#skF_2'),C_267)
      | ~ v1_relat_1(C_267)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_6508])).

tff(c_8185,plain,(
    ! [C_300] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_300)) = k5_relat_1(k6_partfun1('#skF_2'),C_300)
      | ~ v1_relat_1(C_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82,c_66,c_1762,c_137,c_6767])).

tff(c_8260,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2624,c_8185])).

tff(c_8319,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2786,c_8260])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_322,plain,(
    ! [A_89,B_90] :
      ( k5_relat_1(k6_partfun1(A_89),B_90) = B_90
      | ~ r1_tarski(k1_relat_1(B_90),A_89)
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_20])).

tff(c_344,plain,(
    ! [A_3,B_4] :
      ( k5_relat_1(k6_partfun1(A_3),B_4) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_322])).

tff(c_8510,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8319,c_344])).

tff(c_8549,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_216,c_8510])).

tff(c_8551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_8549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.27/3.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.46/3.06  
% 8.46/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.46/3.06  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.46/3.06  
% 8.46/3.06  %Foreground sorts:
% 8.46/3.06  
% 8.46/3.06  
% 8.46/3.06  %Background operators:
% 8.46/3.06  
% 8.46/3.06  
% 8.46/3.06  %Foreground operators:
% 8.46/3.06  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.46/3.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.46/3.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.46/3.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.46/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.46/3.06  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.46/3.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.46/3.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.46/3.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.46/3.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.46/3.06  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.46/3.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.46/3.06  tff('#skF_2', type, '#skF_2': $i).
% 8.46/3.06  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.46/3.06  tff('#skF_3', type, '#skF_3': $i).
% 8.46/3.06  tff('#skF_1', type, '#skF_1': $i).
% 8.46/3.06  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.46/3.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.46/3.06  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.46/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.46/3.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.46/3.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.46/3.06  tff('#skF_4', type, '#skF_4': $i).
% 8.46/3.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.46/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.46/3.06  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.46/3.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.46/3.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.46/3.06  
% 8.46/3.08  tff(f_172, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 8.46/3.08  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.46/3.08  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.46/3.08  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.46/3.08  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.46/3.08  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.46/3.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.46/3.08  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.46/3.08  tff(f_146, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.46/3.08  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.46/3.08  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.46/3.08  tff(f_134, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.46/3.08  tff(f_118, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.46/3.08  tff(f_144, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.46/3.08  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 8.46/3.08  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 8.46/3.08  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 8.46/3.08  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 8.46/3.08  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 8.46/3.08  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.46/3.08  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.46/3.08  tff(c_126, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.46/3.08  tff(c_138, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_126])).
% 8.46/3.08  tff(c_203, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.46/3.08  tff(c_216, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_203])).
% 8.46/3.08  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.46/3.08  tff(c_137, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_126])).
% 8.46/3.08  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.46/3.08  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.46/3.08  tff(c_26, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.46/3.08  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.46/3.08  tff(c_359, plain, (![A_95, B_96, C_97]: (k2_relset_1(A_95, B_96, C_97)=k2_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.46/3.08  tff(c_365, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_359])).
% 8.46/3.08  tff(c_372, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_365])).
% 8.46/3.08  tff(c_301, plain, (![A_88]: (k1_relat_1(k2_funct_1(A_88))=k2_relat_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.46/3.08  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.46/3.08  tff(c_184, plain, (![B_70, A_71]: (v4_relat_1(B_70, A_71) | ~r1_tarski(k1_relat_1(B_70), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.46/3.08  tff(c_194, plain, (![B_70]: (v4_relat_1(B_70, k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_6, c_184])).
% 8.46/3.08  tff(c_1739, plain, (![A_160]: (v4_relat_1(k2_funct_1(A_160), k2_relat_1(A_160)) | ~v1_relat_1(k2_funct_1(A_160)) | ~v2_funct_1(A_160) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(superposition, [status(thm), theory('equality')], [c_301, c_194])).
% 8.46/3.08  tff(c_1742, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_372, c_1739])).
% 8.46/3.08  tff(c_1750, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_82, c_66, c_1742])).
% 8.46/3.08  tff(c_1753, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1750])).
% 8.46/3.08  tff(c_1756, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1753])).
% 8.46/3.08  tff(c_1760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_82, c_1756])).
% 8.46/3.08  tff(c_1762, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1750])).
% 8.46/3.08  tff(c_215, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_203])).
% 8.46/3.08  tff(c_58, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.46/3.08  tff(c_16, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.46/3.08  tff(c_88, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16])).
% 8.46/3.08  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.46/3.08  tff(c_1694, plain, (![B_159, D_158, A_154, F_155, E_157, C_156]: (m1_subset_1(k1_partfun1(A_154, B_159, C_156, D_158, E_157, F_155), k1_zfmisc_1(k2_zfmisc_1(A_154, D_158))) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(C_156, D_158))) | ~v1_funct_1(F_155) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_154, B_159))) | ~v1_funct_1(E_157))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.46/3.08  tff(c_54, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.46/3.08  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.46/3.08  tff(c_875, plain, (![D_118, C_119, A_120, B_121]: (D_118=C_119 | ~r2_relset_1(A_120, B_121, C_119, D_118) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.46/3.08  tff(c_883, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_875])).
% 8.46/3.08  tff(c_898, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_883])).
% 8.46/3.08  tff(c_1081, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_898])).
% 8.46/3.08  tff(c_1707, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1694, c_1081])).
% 8.46/3.08  tff(c_1729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_1707])).
% 8.46/3.08  tff(c_1730, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_898])).
% 8.46/3.08  tff(c_2238, plain, (![D_177, B_178, C_181, F_180, E_176, A_179]: (k1_partfun1(A_179, B_178, C_181, D_177, E_176, F_180)=k5_relat_1(E_176, F_180) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(C_181, D_177))) | ~v1_funct_1(F_180) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))) | ~v1_funct_1(E_176))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.46/3.08  tff(c_2244, plain, (![A_179, B_178, E_176]: (k1_partfun1(A_179, B_178, '#skF_2', '#skF_1', E_176, '#skF_4')=k5_relat_1(E_176, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))) | ~v1_funct_1(E_176))), inference(resolution, [status(thm)], [c_72, c_2238])).
% 8.46/3.08  tff(c_2607, plain, (![A_195, B_196, E_197]: (k1_partfun1(A_195, B_196, '#skF_2', '#skF_1', E_197, '#skF_4')=k5_relat_1(E_197, '#skF_4') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~v1_funct_1(E_197))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2244])).
% 8.46/3.08  tff(c_2616, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2607])).
% 8.46/3.08  tff(c_2624, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1730, c_2616])).
% 8.46/3.08  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k1_relat_1(k5_relat_1(A_5, B_7)), k1_relat_1(A_5)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.46/3.08  tff(c_2649, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2624, c_12])).
% 8.46/3.08  tff(c_2665, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_138, c_88, c_2649])).
% 8.46/3.08  tff(c_217, plain, (![B_79, A_80]: (r1_tarski(k1_relat_1(B_79), A_80) | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.46/3.08  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.46/3.08  tff(c_227, plain, (![B_79, A_80]: (k1_relat_1(B_79)=A_80 | ~r1_tarski(A_80, k1_relat_1(B_79)) | ~v4_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_217, c_2])).
% 8.46/3.08  tff(c_2669, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2665, c_227])).
% 8.46/3.08  tff(c_2674, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_215, c_2669])).
% 8.46/3.08  tff(c_289, plain, (![A_87]: (k2_relat_1(k2_funct_1(A_87))=k1_relat_1(A_87) | ~v2_funct_1(A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.46/3.08  tff(c_22, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.46/3.08  tff(c_85, plain, (![A_18]: (k5_relat_1(A_18, k6_partfun1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 8.46/3.08  tff(c_2747, plain, (![A_198]: (k5_relat_1(k2_funct_1(A_198), k6_partfun1(k1_relat_1(A_198)))=k2_funct_1(A_198) | ~v1_relat_1(k2_funct_1(A_198)) | ~v2_funct_1(A_198) | ~v1_funct_1(A_198) | ~v1_relat_1(A_198))), inference(superposition, [status(thm), theory('equality')], [c_289, c_85])).
% 8.46/3.08  tff(c_2768, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2674, c_2747])).
% 8.46/3.08  tff(c_2786, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_82, c_66, c_1762, c_2768])).
% 8.46/3.08  tff(c_32, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_relat_1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.46/3.08  tff(c_752, plain, (![A_113]: (k5_relat_1(k2_funct_1(A_113), A_113)=k6_partfun1(k2_relat_1(A_113)) | ~v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 8.46/3.08  tff(c_14, plain, (![A_8, B_12, C_14]: (k5_relat_1(k5_relat_1(A_8, B_12), C_14)=k5_relat_1(A_8, k5_relat_1(B_12, C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.46/3.08  tff(c_6508, plain, (![A_266, C_267]: (k5_relat_1(k6_partfun1(k2_relat_1(A_266)), C_267)=k5_relat_1(k2_funct_1(A_266), k5_relat_1(A_266, C_267)) | ~v1_relat_1(C_267) | ~v1_relat_1(A_266) | ~v1_relat_1(k2_funct_1(A_266)) | ~v2_funct_1(A_266) | ~v1_funct_1(A_266) | ~v1_relat_1(A_266))), inference(superposition, [status(thm), theory('equality')], [c_752, c_14])).
% 8.46/3.08  tff(c_6767, plain, (![C_267]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_267))=k5_relat_1(k6_partfun1('#skF_2'), C_267) | ~v1_relat_1(C_267) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_372, c_6508])).
% 8.46/3.08  tff(c_8185, plain, (![C_300]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_300))=k5_relat_1(k6_partfun1('#skF_2'), C_300) | ~v1_relat_1(C_300))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_82, c_66, c_1762, c_137, c_6767])).
% 8.46/3.08  tff(c_8260, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2624, c_8185])).
% 8.46/3.08  tff(c_8319, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_2786, c_8260])).
% 8.46/3.08  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.46/3.08  tff(c_20, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.46/3.08  tff(c_322, plain, (![A_89, B_90]: (k5_relat_1(k6_partfun1(A_89), B_90)=B_90 | ~r1_tarski(k1_relat_1(B_90), A_89) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_20])).
% 8.46/3.08  tff(c_344, plain, (![A_3, B_4]: (k5_relat_1(k6_partfun1(A_3), B_4)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_322])).
% 8.46/3.08  tff(c_8510, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8319, c_344])).
% 8.46/3.08  tff(c_8549, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_216, c_8510])).
% 8.46/3.08  tff(c_8551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_8549])).
% 8.46/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.46/3.08  
% 8.46/3.08  Inference rules
% 8.46/3.08  ----------------------
% 8.46/3.08  #Ref     : 0
% 8.46/3.08  #Sup     : 1765
% 8.46/3.08  #Fact    : 0
% 8.46/3.08  #Define  : 0
% 8.46/3.08  #Split   : 7
% 8.46/3.08  #Chain   : 0
% 8.46/3.08  #Close   : 0
% 8.46/3.08  
% 8.46/3.08  Ordering : KBO
% 8.46/3.08  
% 8.46/3.08  Simplification rules
% 8.46/3.08  ----------------------
% 8.46/3.08  #Subsume      : 143
% 8.46/3.08  #Demod        : 3143
% 8.46/3.08  #Tautology    : 683
% 8.46/3.08  #SimpNegUnit  : 1
% 8.46/3.08  #BackRed      : 15
% 8.46/3.08  
% 8.46/3.08  #Partial instantiations: 0
% 8.46/3.08  #Strategies tried      : 1
% 8.46/3.08  
% 8.46/3.08  Timing (in seconds)
% 8.46/3.08  ----------------------
% 8.46/3.09  Preprocessing        : 0.42
% 8.46/3.09  Parsing              : 0.24
% 8.46/3.09  CNF conversion       : 0.03
% 8.46/3.09  Main loop            : 1.74
% 8.46/3.09  Inferencing          : 0.51
% 8.46/3.09  Reduction            : 0.77
% 8.46/3.09  Demodulation         : 0.61
% 8.46/3.09  BG Simplification    : 0.06
% 8.46/3.09  Subsumption          : 0.30
% 8.46/3.09  Abstraction          : 0.07
% 8.46/3.09  MUC search           : 0.00
% 8.46/3.09  Cooper               : 0.00
% 8.46/3.09  Total                : 2.21
% 8.46/3.09  Index Insertion      : 0.00
% 8.46/3.09  Index Deletion       : 0.00
% 8.46/3.09  Index Matching       : 0.00
% 8.46/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
