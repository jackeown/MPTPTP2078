%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:38 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 632 expanded)
%              Number of leaves         :   44 ( 236 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 (1834 expanded)
%              Number of equality atoms :   83 ( 500 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_158,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_134,axiom,(
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

tff(f_156,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_146,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ( k1_relat_1(B) = A
              & k1_relat_1(C) = A
              & r1_tarski(k2_relat_1(C),A)
              & v2_funct_1(B)
              & k5_relat_1(C,B) = B )
           => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_755,plain,(
    ! [A_133,B_134,D_135] :
      ( r2_relset_1(A_133,B_134,D_135,D_135)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_774,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_755])).

tff(c_297,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_322,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_297])).

tff(c_576,plain,(
    ! [C_106,B_107,A_108] :
      ( v5_relat_1(C_106,B_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_602,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_576])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_323,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_297])).

tff(c_90,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_30,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_30])).

tff(c_34,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94,plain,(
    ! [A_15] : v1_relat_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34])).

tff(c_176,plain,(
    ! [A_66] :
      ( k1_relat_1(A_66) != k1_xboole_0
      | k1_xboole_0 = A_66
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_179,plain,(
    ! [A_15] :
      ( k1_relat_1(k6_partfun1(A_15)) != k1_xboole_0
      | k6_partfun1(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_176])).

tff(c_189,plain,(
    ! [A_68] :
      ( k1_xboole_0 != A_68
      | k6_partfun1(A_68) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_179])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_195,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_74])).

tff(c_220,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_88,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_832,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_860,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_832])).

tff(c_1106,plain,(
    ! [B_182,A_183,C_184] :
      ( k1_xboole_0 = B_182
      | k1_relset_1(A_183,B_182,C_184) = A_183
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1119,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_1106])).

tff(c_1139,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_860,c_1119])).

tff(c_1140,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_1139])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_859,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_832])).

tff(c_1116,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_1106])).

tff(c_1135,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_859,c_1116])).

tff(c_1136,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_1135])).

tff(c_76,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1521,plain,(
    ! [F_214,E_217,B_216,A_215,C_212,D_213] :
      ( k1_partfun1(A_215,B_216,C_212,D_213,E_217,F_214) = k5_relat_1(E_217,F_214)
      | ~ m1_subset_1(F_214,k1_zfmisc_1(k2_zfmisc_1(C_212,D_213)))
      | ~ v1_funct_1(F_214)
      | ~ m1_subset_1(E_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_1(E_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1530,plain,(
    ! [A_215,B_216,E_217] :
      ( k1_partfun1(A_215,B_216,'#skF_1','#skF_1',E_217,'#skF_2') = k5_relat_1(E_217,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_1(E_217) ) ),
    inference(resolution,[status(thm)],[c_86,c_1521])).

tff(c_1687,plain,(
    ! [A_230,B_231,E_232] :
      ( k1_partfun1(A_230,B_231,'#skF_1','#skF_1',E_232,'#skF_2') = k5_relat_1(E_232,'#skF_2')
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231)))
      | ~ v1_funct_1(E_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1530])).

tff(c_1697,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1687])).

tff(c_1715,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1697])).

tff(c_66,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] :
      ( m1_subset_1(k1_partfun1(A_37,B_38,C_39,D_40,E_41,F_42),k1_zfmisc_1(k2_zfmisc_1(A_37,D_40)))
      | ~ m1_subset_1(F_42,k1_zfmisc_1(k2_zfmisc_1(C_39,D_40)))
      | ~ v1_funct_1(F_42)
      | ~ m1_subset_1(E_41,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_1(E_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1962,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1715,c_66])).

tff(c_1966,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_90,c_86,c_1962])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1219,plain,(
    ! [D_191,C_192,A_193,B_194] :
      ( D_191 = C_192
      | ~ r2_relset_1(A_193,B_194,C_192,D_191)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1233,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_1219])).

tff(c_1258,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1233])).

tff(c_2690,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1966,c_1715,c_1715,c_1258])).

tff(c_38,plain,(
    ! [C_19,B_17] :
      ( k6_relat_1(k1_relat_1(C_19)) = C_19
      | k5_relat_1(C_19,B_17) != B_17
      | ~ v2_funct_1(B_17)
      | ~ r1_tarski(k2_relat_1(C_19),k1_relat_1(C_19))
      | k1_relat_1(C_19) != k1_relat_1(B_17)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_92,plain,(
    ! [C_19,B_17] :
      ( k6_partfun1(k1_relat_1(C_19)) = C_19
      | k5_relat_1(C_19,B_17) != B_17
      | ~ v2_funct_1(B_17)
      | ~ r1_tarski(k2_relat_1(C_19),k1_relat_1(C_19))
      | k1_relat_1(C_19) != k1_relat_1(B_17)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_38])).

tff(c_2710,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k1_relat_1('#skF_2') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2690,c_92])).

tff(c_2715,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_90,c_322,c_84,c_1140,c_1136,c_1136,c_76,c_1136,c_2710])).

tff(c_2717,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2715])).

tff(c_2729,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2717])).

tff(c_2737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_602,c_2729])).

tff(c_2738,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2715])).

tff(c_2740,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2738,c_74])).

tff(c_2743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_2740])).

tff(c_2745,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2764,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_14])).

tff(c_3273,plain,(
    ! [A_349,B_350,D_351] :
      ( r2_relset_1(A_349,B_350,D_351,D_351)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(k2_zfmisc_1(A_349,B_350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3286,plain,(
    ! [A_349,B_350] : r2_relset_1(A_349,B_350,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2764,c_3273])).

tff(c_32,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    ! [A_14] : k2_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_32])).

tff(c_182,plain,(
    ! [A_67] :
      ( k2_relat_1(A_67) != k1_xboole_0
      | k1_xboole_0 = A_67
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_185,plain,(
    ! [A_15] :
      ( k2_relat_1(k6_partfun1(A_15)) != k1_xboole_0
      | k6_partfun1(A_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_182])).

tff(c_187,plain,(
    ! [A_15] :
      ( k1_xboole_0 != A_15
      | k6_partfun1(A_15) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_185])).

tff(c_2884,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_2745,c_187])).

tff(c_158,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_174,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_2760,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_174])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2763,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_2745,c_12])).

tff(c_172,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_158])).

tff(c_2776,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_172])).

tff(c_2819,plain,(
    ! [B_294,A_295] :
      ( B_294 = A_295
      | ~ r1_tarski(B_294,A_295)
      | ~ r1_tarski(A_295,B_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2821,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_2776,c_2819])).

tff(c_2830,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2760,c_2821])).

tff(c_2842,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2830,c_74])).

tff(c_2910,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_2842])).

tff(c_3291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3286,c_2910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:44:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.97  
% 5.14/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.97  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.14/1.97  
% 5.14/1.97  %Foreground sorts:
% 5.14/1.97  
% 5.14/1.97  
% 5.14/1.97  %Background operators:
% 5.14/1.97  
% 5.14/1.97  
% 5.14/1.97  %Foreground operators:
% 5.14/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.14/1.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.14/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/1.97  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.14/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/1.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.14/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.14/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.14/1.97  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.14/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.14/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.14/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.14/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.14/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.14/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.14/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.14/1.97  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.14/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.14/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.14/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.14/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.14/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.14/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.14/1.97  
% 5.35/1.99  tff(f_178, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 5.35/1.99  tff(f_114, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.35/1.99  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.35/1.99  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.35/1.99  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.35/1.99  tff(f_158, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.35/1.99  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.35/1.99  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.35/1.99  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.35/1.99  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.35/1.99  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.35/1.99  tff(f_156, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.35/1.99  tff(f_146, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.35/1.99  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 5.35/1.99  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.35/1.99  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.35/1.99  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.35/1.99  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.35/1.99  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_755, plain, (![A_133, B_134, D_135]: (r2_relset_1(A_133, B_134, D_135, D_135) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.35/1.99  tff(c_774, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_755])).
% 5.35/1.99  tff(c_297, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.35/1.99  tff(c_322, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_297])).
% 5.35/1.99  tff(c_576, plain, (![C_106, B_107, A_108]: (v5_relat_1(C_106, B_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.35/1.99  tff(c_602, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_576])).
% 5.35/1.99  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.35/1.99  tff(c_86, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_323, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_297])).
% 5.35/1.99  tff(c_90, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_72, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.35/1.99  tff(c_30, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.35/1.99  tff(c_96, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_30])).
% 5.35/1.99  tff(c_34, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.35/1.99  tff(c_94, plain, (![A_15]: (v1_relat_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_34])).
% 5.35/1.99  tff(c_176, plain, (![A_66]: (k1_relat_1(A_66)!=k1_xboole_0 | k1_xboole_0=A_66 | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.35/1.99  tff(c_179, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))!=k1_xboole_0 | k6_partfun1(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_176])).
% 5.35/1.99  tff(c_189, plain, (![A_68]: (k1_xboole_0!=A_68 | k6_partfun1(A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_179])).
% 5.35/1.99  tff(c_74, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_195, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_189, c_74])).
% 5.35/1.99  tff(c_220, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_195])).
% 5.35/1.99  tff(c_88, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_832, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.35/1.99  tff(c_860, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_86, c_832])).
% 5.35/1.99  tff(c_1106, plain, (![B_182, A_183, C_184]: (k1_xboole_0=B_182 | k1_relset_1(A_183, B_182, C_184)=A_183 | ~v1_funct_2(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.35/1.99  tff(c_1119, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_1106])).
% 5.35/1.99  tff(c_1139, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_860, c_1119])).
% 5.35/1.99  tff(c_1140, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_220, c_1139])).
% 5.35/1.99  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_859, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_832])).
% 5.35/1.99  tff(c_1116, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_1106])).
% 5.35/1.99  tff(c_1135, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_859, c_1116])).
% 5.35/1.99  tff(c_1136, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_220, c_1135])).
% 5.35/1.99  tff(c_76, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_1521, plain, (![F_214, E_217, B_216, A_215, C_212, D_213]: (k1_partfun1(A_215, B_216, C_212, D_213, E_217, F_214)=k5_relat_1(E_217, F_214) | ~m1_subset_1(F_214, k1_zfmisc_1(k2_zfmisc_1(C_212, D_213))) | ~v1_funct_1(F_214) | ~m1_subset_1(E_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_1(E_217))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.35/1.99  tff(c_1530, plain, (![A_215, B_216, E_217]: (k1_partfun1(A_215, B_216, '#skF_1', '#skF_1', E_217, '#skF_2')=k5_relat_1(E_217, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_1(E_217))), inference(resolution, [status(thm)], [c_86, c_1521])).
% 5.35/1.99  tff(c_1687, plain, (![A_230, B_231, E_232]: (k1_partfun1(A_230, B_231, '#skF_1', '#skF_1', E_232, '#skF_2')=k5_relat_1(E_232, '#skF_2') | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))) | ~v1_funct_1(E_232))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1530])).
% 5.35/1.99  tff(c_1697, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1687])).
% 5.35/1.99  tff(c_1715, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1697])).
% 5.35/1.99  tff(c_66, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (m1_subset_1(k1_partfun1(A_37, B_38, C_39, D_40, E_41, F_42), k1_zfmisc_1(k2_zfmisc_1(A_37, D_40))) | ~m1_subset_1(F_42, k1_zfmisc_1(k2_zfmisc_1(C_39, D_40))) | ~v1_funct_1(F_42) | ~m1_subset_1(E_41, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_1(E_41))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.35/1.99  tff(c_1962, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1715, c_66])).
% 5.35/1.99  tff(c_1966, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_90, c_86, c_1962])).
% 5.35/1.99  tff(c_78, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.35/1.99  tff(c_1219, plain, (![D_191, C_192, A_193, B_194]: (D_191=C_192 | ~r2_relset_1(A_193, B_194, C_192, D_191) | ~m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.35/1.99  tff(c_1233, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_78, c_1219])).
% 5.35/1.99  tff(c_1258, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1233])).
% 5.35/1.99  tff(c_2690, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1966, c_1715, c_1715, c_1258])).
% 5.35/1.99  tff(c_38, plain, (![C_19, B_17]: (k6_relat_1(k1_relat_1(C_19))=C_19 | k5_relat_1(C_19, B_17)!=B_17 | ~v2_funct_1(B_17) | ~r1_tarski(k2_relat_1(C_19), k1_relat_1(C_19)) | k1_relat_1(C_19)!=k1_relat_1(B_17) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.35/1.99  tff(c_92, plain, (![C_19, B_17]: (k6_partfun1(k1_relat_1(C_19))=C_19 | k5_relat_1(C_19, B_17)!=B_17 | ~v2_funct_1(B_17) | ~r1_tarski(k2_relat_1(C_19), k1_relat_1(C_19)) | k1_relat_1(C_19)!=k1_relat_1(B_17) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_38])).
% 5.35/1.99  tff(c_2710, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v2_funct_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k1_relat_1('#skF_2')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2690, c_92])).
% 5.35/1.99  tff(c_2715, plain, (k6_partfun1('#skF_1')='#skF_3' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_90, c_322, c_84, c_1140, c_1136, c_1136, c_76, c_1136, c_2710])).
% 5.35/1.99  tff(c_2717, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_2715])).
% 5.35/1.99  tff(c_2729, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2717])).
% 5.35/1.99  tff(c_2737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_322, c_602, c_2729])).
% 5.35/1.99  tff(c_2738, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_2715])).
% 5.35/1.99  tff(c_2740, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2738, c_74])).
% 5.35/1.99  tff(c_2743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_774, c_2740])).
% 5.35/1.99  tff(c_2745, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_195])).
% 5.35/1.99  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.35/1.99  tff(c_2764, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_14])).
% 5.35/1.99  tff(c_3273, plain, (![A_349, B_350, D_351]: (r2_relset_1(A_349, B_350, D_351, D_351) | ~m1_subset_1(D_351, k1_zfmisc_1(k2_zfmisc_1(A_349, B_350))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.35/1.99  tff(c_3286, plain, (![A_349, B_350]: (r2_relset_1(A_349, B_350, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_2764, c_3273])).
% 5.35/1.99  tff(c_32, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.35/1.99  tff(c_95, plain, (![A_14]: (k2_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_32])).
% 5.35/1.99  tff(c_182, plain, (![A_67]: (k2_relat_1(A_67)!=k1_xboole_0 | k1_xboole_0=A_67 | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.35/1.99  tff(c_185, plain, (![A_15]: (k2_relat_1(k6_partfun1(A_15))!=k1_xboole_0 | k6_partfun1(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_182])).
% 5.35/1.99  tff(c_187, plain, (![A_15]: (k1_xboole_0!=A_15 | k6_partfun1(A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_185])).
% 5.35/1.99  tff(c_2884, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_2745, c_187])).
% 5.35/1.99  tff(c_158, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.35/1.99  tff(c_174, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_158])).
% 5.35/1.99  tff(c_2760, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_174])).
% 5.35/1.99  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.35/1.99  tff(c_2763, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_2745, c_12])).
% 5.35/1.99  tff(c_172, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_158])).
% 5.35/1.99  tff(c_2776, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2763, c_172])).
% 5.35/1.99  tff(c_2819, plain, (![B_294, A_295]: (B_294=A_295 | ~r1_tarski(B_294, A_295) | ~r1_tarski(A_295, B_294))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.35/1.99  tff(c_2821, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_2776, c_2819])).
% 5.35/1.99  tff(c_2830, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2760, c_2821])).
% 5.35/1.99  tff(c_2842, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2830, c_74])).
% 5.35/1.99  tff(c_2910, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_2842])).
% 5.35/1.99  tff(c_3291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3286, c_2910])).
% 5.35/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/1.99  
% 5.35/1.99  Inference rules
% 5.35/1.99  ----------------------
% 5.35/1.99  #Ref     : 6
% 5.35/1.99  #Sup     : 664
% 5.35/1.99  #Fact    : 0
% 5.35/1.99  #Define  : 0
% 5.35/1.99  #Split   : 11
% 5.35/1.99  #Chain   : 0
% 5.35/1.99  #Close   : 0
% 5.35/1.99  
% 5.35/1.99  Ordering : KBO
% 5.35/1.99  
% 5.35/1.99  Simplification rules
% 5.35/1.99  ----------------------
% 5.35/1.99  #Subsume      : 99
% 5.35/1.99  #Demod        : 416
% 5.35/1.99  #Tautology    : 275
% 5.35/1.99  #SimpNegUnit  : 28
% 5.35/1.99  #BackRed      : 50
% 5.35/1.99  
% 5.35/1.99  #Partial instantiations: 0
% 5.35/1.99  #Strategies tried      : 1
% 5.35/1.99  
% 5.35/1.99  Timing (in seconds)
% 5.35/1.99  ----------------------
% 5.35/1.99  Preprocessing        : 0.36
% 5.35/1.99  Parsing              : 0.19
% 5.35/1.99  CNF conversion       : 0.02
% 5.35/1.99  Main loop            : 0.81
% 5.35/1.99  Inferencing          : 0.27
% 5.35/1.99  Reduction            : 0.28
% 5.35/1.99  Demodulation         : 0.20
% 5.35/1.99  BG Simplification    : 0.03
% 5.35/1.99  Subsumption          : 0.16
% 5.35/1.99  Abstraction          : 0.03
% 5.35/1.99  MUC search           : 0.00
% 5.35/1.99  Cooper               : 0.00
% 5.35/1.99  Total                : 1.21
% 5.35/1.99  Index Insertion      : 0.00
% 5.35/1.99  Index Deletion       : 0.00
% 5.35/1.99  Index Matching       : 0.00
% 5.35/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
