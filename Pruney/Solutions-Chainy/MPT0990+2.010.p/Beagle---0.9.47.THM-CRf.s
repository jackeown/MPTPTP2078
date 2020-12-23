%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:56 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.46s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 315 expanded)
%              Number of leaves         :   46 ( 130 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (1089 expanded)
%              Number of equality atoms :   59 ( 304 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_170,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_144,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_120,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_142,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_58,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_131,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_143,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_131])).

tff(c_214,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_227,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_214])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_142,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_131])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_26,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_505,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_511,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_505])).

tff(c_518,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_511])).

tff(c_245,plain,(
    ! [A_82] :
      ( k1_relat_1(k2_funct_1(A_82)) = k2_relat_1(A_82)
      | ~ v2_funct_1(A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [B_64,A_65] :
      ( v4_relat_1(B_64,A_65)
      | ~ r1_tarski(k1_relat_1(B_64),A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    ! [B_64] :
      ( v4_relat_1(B_64,k1_relat_1(B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_1079,plain,(
    ! [A_125] :
      ( v4_relat_1(k2_funct_1(A_125),k2_relat_1(A_125))
      | ~ v1_relat_1(k2_funct_1(A_125))
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_169])).

tff(c_1082,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_1079])).

tff(c_1090,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_64,c_1082])).

tff(c_1730,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1090])).

tff(c_1733,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1730])).

tff(c_1737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_1733])).

tff(c_1739,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1090])).

tff(c_226,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_214])).

tff(c_56,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_16,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_87,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1692,plain,(
    ! [F_153,D_155,A_154,B_156,E_158,C_157] :
      ( m1_subset_1(k1_partfun1(A_154,B_156,C_157,D_155,E_158,F_153),k1_zfmisc_1(k2_zfmisc_1(A_154,D_155)))
      | ~ m1_subset_1(F_153,k1_zfmisc_1(k2_zfmisc_1(C_157,D_155)))
      | ~ v1_funct_1(F_153)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(A_154,B_156)))
      | ~ v1_funct_1(E_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ! [A_35] : m1_subset_1(k6_relat_1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_81,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_932,plain,(
    ! [D_119,C_120,A_121,B_122] :
      ( D_119 = C_120
      | ~ r2_relset_1(A_121,B_122,C_120,D_119)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_940,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_932])).

tff(c_955,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_940])).

tff(c_1093,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_1705,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1692,c_1093])).

tff(c_1727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1705])).

tff(c_1728,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_2271,plain,(
    ! [B_177,A_178,D_176,C_180,E_175,F_179] :
      ( k1_partfun1(A_178,B_177,C_180,D_176,E_175,F_179) = k5_relat_1(E_175,F_179)
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(C_180,D_176)))
      | ~ v1_funct_1(F_179)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177)))
      | ~ v1_funct_1(E_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2277,plain,(
    ! [A_178,B_177,E_175] :
      ( k1_partfun1(A_178,B_177,'#skF_2','#skF_1',E_175,'#skF_4') = k5_relat_1(E_175,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177)))
      | ~ v1_funct_1(E_175) ) ),
    inference(resolution,[status(thm)],[c_70,c_2271])).

tff(c_3062,plain,(
    ! [A_201,B_202,E_203] :
      ( k1_partfun1(A_201,B_202,'#skF_2','#skF_1',E_203,'#skF_4') = k5_relat_1(E_203,'#skF_4')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_1(E_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2277])).

tff(c_3077,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3062])).

tff(c_3091,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1728,c_3077])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_5,B_7)),k1_relat_1(A_5))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3119,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3091,c_12])).

tff(c_3137,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_143,c_87,c_3119])).

tff(c_201,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_211,plain,(
    ! [B_75,A_76] :
      ( k1_relat_1(B_75) = A_76
      | ~ r1_tarski(A_76,k1_relat_1(B_75))
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_201,c_2])).

tff(c_3141,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3137,c_211])).

tff(c_3146,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_226,c_3141])).

tff(c_412,plain,(
    ! [A_93] :
      ( k2_relat_1(k2_funct_1(A_93)) = k1_relat_1(A_93)
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_84,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_partfun1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_3424,plain,(
    ! [A_205] :
      ( k5_relat_1(k2_funct_1(A_205),k6_partfun1(k1_relat_1(A_205))) = k2_funct_1(A_205)
      | ~ v1_relat_1(k2_funct_1(A_205))
      | ~ v2_funct_1(A_205)
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_84])).

tff(c_3451,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3146,c_3424])).

tff(c_3479,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_64,c_1739,c_3451])).

tff(c_32,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_relat_1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_750,plain,(
    ! [A_112] :
      ( k5_relat_1(k2_funct_1(A_112),A_112) = k6_partfun1(k2_relat_1(A_112))
      | ~ v2_funct_1(A_112)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_14,plain,(
    ! [A_8,B_12,C_14] :
      ( k5_relat_1(k5_relat_1(A_8,B_12),C_14) = k5_relat_1(A_8,k5_relat_1(B_12,C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6763,plain,(
    ! [A_270,C_271] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_270)),C_271) = k5_relat_1(k2_funct_1(A_270),k5_relat_1(A_270,C_271))
      | ~ v1_relat_1(C_271)
      | ~ v1_relat_1(A_270)
      | ~ v1_relat_1(k2_funct_1(A_270))
      | ~ v2_funct_1(A_270)
      | ~ v1_funct_1(A_270)
      | ~ v1_relat_1(A_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_14])).

tff(c_7005,plain,(
    ! [C_271] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_271)) = k5_relat_1(k6_partfun1('#skF_2'),C_271)
      | ~ v1_relat_1(C_271)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_6763])).

tff(c_8754,plain,(
    ! [C_306] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_306)) = k5_relat_1(k6_partfun1('#skF_2'),C_306)
      | ~ v1_relat_1(C_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_64,c_1739,c_142,c_7005])).

tff(c_8835,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3091,c_8754])).

tff(c_8898,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_3479,c_8835])).

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

tff(c_263,plain,(
    ! [A_83,B_84] :
      ( k5_relat_1(k6_partfun1(A_83),B_84) = B_84
      | ~ r1_tarski(k1_relat_1(B_84),A_83)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_277,plain,(
    ! [A_3,B_4] :
      ( k5_relat_1(k6_partfun1(A_3),B_4) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_263])).

tff(c_9103,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8898,c_277])).

tff(c_9142,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_227,c_9103])).

tff(c_9144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_9142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.46/2.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.83  
% 7.46/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.83  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.46/2.83  
% 7.46/2.83  %Foreground sorts:
% 7.46/2.83  
% 7.46/2.83  
% 7.46/2.83  %Background operators:
% 7.46/2.83  
% 7.46/2.83  
% 7.46/2.83  %Foreground operators:
% 7.46/2.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.46/2.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.46/2.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.46/2.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.46/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.46/2.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.46/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.46/2.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.46/2.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.46/2.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.46/2.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.46/2.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.46/2.83  tff('#skF_2', type, '#skF_2': $i).
% 7.46/2.83  tff('#skF_3', type, '#skF_3': $i).
% 7.46/2.83  tff('#skF_1', type, '#skF_1': $i).
% 7.46/2.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.46/2.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.46/2.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.46/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.46/2.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.46/2.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.46/2.83  tff('#skF_4', type, '#skF_4': $i).
% 7.46/2.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.46/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.46/2.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.46/2.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.46/2.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.46/2.83  
% 7.46/2.85  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.46/2.85  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.46/2.85  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.46/2.85  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.46/2.85  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.46/2.85  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.46/2.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.46/2.85  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.46/2.85  tff(f_144, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.46/2.85  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.46/2.85  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.46/2.85  tff(f_120, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.46/2.85  tff(f_118, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.46/2.85  tff(f_142, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.46/2.85  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 7.46/2.85  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 7.46/2.85  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.46/2.85  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.46/2.85  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 7.46/2.85  tff(c_58, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.46/2.85  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.46/2.85  tff(c_131, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.46/2.85  tff(c_143, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_131])).
% 7.46/2.85  tff(c_214, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.46/2.85  tff(c_227, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_214])).
% 7.46/2.85  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.46/2.85  tff(c_142, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_131])).
% 7.46/2.85  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.46/2.85  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.46/2.85  tff(c_26, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.46/2.85  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.46/2.85  tff(c_505, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.46/2.85  tff(c_511, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_505])).
% 7.46/2.85  tff(c_518, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_511])).
% 7.46/2.85  tff(c_245, plain, (![A_82]: (k1_relat_1(k2_funct_1(A_82))=k2_relat_1(A_82) | ~v2_funct_1(A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.46/2.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.46/2.85  tff(c_159, plain, (![B_64, A_65]: (v4_relat_1(B_64, A_65) | ~r1_tarski(k1_relat_1(B_64), A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.46/2.85  tff(c_169, plain, (![B_64]: (v4_relat_1(B_64, k1_relat_1(B_64)) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_6, c_159])).
% 7.46/2.85  tff(c_1079, plain, (![A_125]: (v4_relat_1(k2_funct_1(A_125), k2_relat_1(A_125)) | ~v1_relat_1(k2_funct_1(A_125)) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_245, c_169])).
% 7.46/2.85  tff(c_1082, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_1079])).
% 7.46/2.85  tff(c_1090, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_64, c_1082])).
% 7.46/2.85  tff(c_1730, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1090])).
% 7.46/2.85  tff(c_1733, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1730])).
% 7.46/2.85  tff(c_1737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_1733])).
% 7.46/2.85  tff(c_1739, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1090])).
% 7.46/2.85  tff(c_226, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_214])).
% 7.46/2.85  tff(c_56, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.46/2.85  tff(c_16, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.46/2.85  tff(c_87, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_16])).
% 7.46/2.85  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.46/2.85  tff(c_1692, plain, (![F_153, D_155, A_154, B_156, E_158, C_157]: (m1_subset_1(k1_partfun1(A_154, B_156, C_157, D_155, E_158, F_153), k1_zfmisc_1(k2_zfmisc_1(A_154, D_155))) | ~m1_subset_1(F_153, k1_zfmisc_1(k2_zfmisc_1(C_157, D_155))) | ~v1_funct_1(F_153) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(A_154, B_156))) | ~v1_funct_1(E_158))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.46/2.85  tff(c_48, plain, (![A_35]: (m1_subset_1(k6_relat_1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.46/2.85  tff(c_81, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48])).
% 7.46/2.85  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.46/2.85  tff(c_932, plain, (![D_119, C_120, A_121, B_122]: (D_119=C_120 | ~r2_relset_1(A_121, B_122, C_120, D_119) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.46/2.85  tff(c_940, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_932])).
% 7.46/2.85  tff(c_955, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_940])).
% 7.46/2.85  tff(c_1093, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_955])).
% 7.46/2.85  tff(c_1705, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1692, c_1093])).
% 7.46/2.85  tff(c_1727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1705])).
% 7.46/2.85  tff(c_1728, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_955])).
% 7.46/2.85  tff(c_2271, plain, (![B_177, A_178, D_176, C_180, E_175, F_179]: (k1_partfun1(A_178, B_177, C_180, D_176, E_175, F_179)=k5_relat_1(E_175, F_179) | ~m1_subset_1(F_179, k1_zfmisc_1(k2_zfmisc_1(C_180, D_176))) | ~v1_funct_1(F_179) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))) | ~v1_funct_1(E_175))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.46/2.85  tff(c_2277, plain, (![A_178, B_177, E_175]: (k1_partfun1(A_178, B_177, '#skF_2', '#skF_1', E_175, '#skF_4')=k5_relat_1(E_175, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))) | ~v1_funct_1(E_175))), inference(resolution, [status(thm)], [c_70, c_2271])).
% 7.46/2.85  tff(c_3062, plain, (![A_201, B_202, E_203]: (k1_partfun1(A_201, B_202, '#skF_2', '#skF_1', E_203, '#skF_4')=k5_relat_1(E_203, '#skF_4') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~v1_funct_1(E_203))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2277])).
% 7.46/2.85  tff(c_3077, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_3062])).
% 7.46/2.85  tff(c_3091, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1728, c_3077])).
% 7.46/2.85  tff(c_12, plain, (![A_5, B_7]: (r1_tarski(k1_relat_1(k5_relat_1(A_5, B_7)), k1_relat_1(A_5)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.46/2.85  tff(c_3119, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3091, c_12])).
% 7.46/2.85  tff(c_3137, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_143, c_87, c_3119])).
% 7.46/2.85  tff(c_201, plain, (![B_75, A_76]: (r1_tarski(k1_relat_1(B_75), A_76) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.46/2.85  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.46/2.85  tff(c_211, plain, (![B_75, A_76]: (k1_relat_1(B_75)=A_76 | ~r1_tarski(A_76, k1_relat_1(B_75)) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_201, c_2])).
% 7.46/2.85  tff(c_3141, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3137, c_211])).
% 7.46/2.85  tff(c_3146, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_226, c_3141])).
% 7.46/2.85  tff(c_412, plain, (![A_93]: (k2_relat_1(k2_funct_1(A_93))=k1_relat_1(A_93) | ~v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.46/2.85  tff(c_22, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.46/2.85  tff(c_84, plain, (![A_18]: (k5_relat_1(A_18, k6_partfun1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_22])).
% 7.46/2.85  tff(c_3424, plain, (![A_205]: (k5_relat_1(k2_funct_1(A_205), k6_partfun1(k1_relat_1(A_205)))=k2_funct_1(A_205) | ~v1_relat_1(k2_funct_1(A_205)) | ~v2_funct_1(A_205) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(superposition, [status(thm), theory('equality')], [c_412, c_84])).
% 7.46/2.85  tff(c_3451, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3146, c_3424])).
% 7.46/2.85  tff(c_3479, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_64, c_1739, c_3451])).
% 7.46/2.85  tff(c_32, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_relat_1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.46/2.85  tff(c_750, plain, (![A_112]: (k5_relat_1(k2_funct_1(A_112), A_112)=k6_partfun1(k2_relat_1(A_112)) | ~v2_funct_1(A_112) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 7.46/2.85  tff(c_14, plain, (![A_8, B_12, C_14]: (k5_relat_1(k5_relat_1(A_8, B_12), C_14)=k5_relat_1(A_8, k5_relat_1(B_12, C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.46/2.85  tff(c_6763, plain, (![A_270, C_271]: (k5_relat_1(k6_partfun1(k2_relat_1(A_270)), C_271)=k5_relat_1(k2_funct_1(A_270), k5_relat_1(A_270, C_271)) | ~v1_relat_1(C_271) | ~v1_relat_1(A_270) | ~v1_relat_1(k2_funct_1(A_270)) | ~v2_funct_1(A_270) | ~v1_funct_1(A_270) | ~v1_relat_1(A_270))), inference(superposition, [status(thm), theory('equality')], [c_750, c_14])).
% 7.46/2.85  tff(c_7005, plain, (![C_271]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_271))=k5_relat_1(k6_partfun1('#skF_2'), C_271) | ~v1_relat_1(C_271) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_518, c_6763])).
% 7.46/2.85  tff(c_8754, plain, (![C_306]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_306))=k5_relat_1(k6_partfun1('#skF_2'), C_306) | ~v1_relat_1(C_306))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_64, c_1739, c_142, c_7005])).
% 7.46/2.85  tff(c_8835, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3091, c_8754])).
% 7.46/2.85  tff(c_8898, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_3479, c_8835])).
% 7.46/2.85  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.46/2.85  tff(c_20, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.46/2.85  tff(c_263, plain, (![A_83, B_84]: (k5_relat_1(k6_partfun1(A_83), B_84)=B_84 | ~r1_tarski(k1_relat_1(B_84), A_83) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20])).
% 7.46/2.85  tff(c_277, plain, (![A_3, B_4]: (k5_relat_1(k6_partfun1(A_3), B_4)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_263])).
% 7.46/2.85  tff(c_9103, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8898, c_277])).
% 7.46/2.85  tff(c_9142, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_227, c_9103])).
% 7.46/2.85  tff(c_9144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_9142])).
% 7.46/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.46/2.85  
% 7.46/2.85  Inference rules
% 7.46/2.85  ----------------------
% 7.46/2.85  #Ref     : 0
% 7.46/2.85  #Sup     : 1898
% 7.46/2.85  #Fact    : 0
% 7.46/2.85  #Define  : 0
% 7.46/2.85  #Split   : 7
% 7.46/2.85  #Chain   : 0
% 7.46/2.85  #Close   : 0
% 7.46/2.85  
% 7.46/2.85  Ordering : KBO
% 7.46/2.85  
% 7.46/2.85  Simplification rules
% 7.46/2.85  ----------------------
% 7.46/2.85  #Subsume      : 148
% 7.46/2.85  #Demod        : 3352
% 7.46/2.85  #Tautology    : 703
% 7.46/2.85  #SimpNegUnit  : 1
% 7.46/2.85  #BackRed      : 16
% 7.46/2.85  
% 7.46/2.85  #Partial instantiations: 0
% 7.46/2.85  #Strategies tried      : 1
% 7.46/2.85  
% 7.46/2.85  Timing (in seconds)
% 7.46/2.85  ----------------------
% 7.46/2.85  Preprocessing        : 0.36
% 7.46/2.85  Parsing              : 0.19
% 7.46/2.85  CNF conversion       : 0.02
% 7.46/2.85  Main loop            : 1.67
% 7.46/2.85  Inferencing          : 0.51
% 7.46/2.85  Reduction            : 0.73
% 7.46/2.85  Demodulation         : 0.59
% 7.46/2.85  BG Simplification    : 0.06
% 7.46/2.85  Subsumption          : 0.28
% 7.46/2.85  Abstraction          : 0.07
% 7.46/2.85  MUC search           : 0.00
% 7.46/2.85  Cooper               : 0.00
% 7.46/2.85  Total                : 2.07
% 7.46/2.85  Index Insertion      : 0.00
% 7.46/2.85  Index Deletion       : 0.00
% 7.46/2.85  Index Matching       : 0.00
% 7.46/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
