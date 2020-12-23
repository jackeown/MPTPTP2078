%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:55 EST 2020

% Result     : Theorem 11.31s
% Output     : CNFRefutation 11.31s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 754 expanded)
%              Number of leaves         :   46 ( 293 expanded)
%              Depth                    :   20
%              Number of atoms          :  255 (2895 expanded)
%              Number of equality atoms :   60 ( 785 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_145,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_217,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_225,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_217])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_238,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_60])).

tff(c_108,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_116,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_108])).

tff(c_128,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_136,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_128])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_115,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_108])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_20,plain,(
    ! [A_12] :
      ( v1_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_22,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_208,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_215,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_208])).

tff(c_471,plain,(
    ! [B_116,A_117,C_118] :
      ( k1_xboole_0 = B_116
      | k1_relset_1(A_117,B_116,C_118) = A_117
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_474,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_471])).

tff(c_480,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_215,c_474])).

tff(c_481,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_480])).

tff(c_18,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_301,plain,(
    ! [A_91] :
      ( k5_relat_1(A_91,k2_funct_1(A_91)) = k6_relat_1(k1_relat_1(A_91))
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_8,B_10)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_307,plain,(
    ! [A_91] :
      ( r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_91))),k2_relat_1(k2_funct_1(A_91)))
      | ~ v1_relat_1(k2_funct_1(A_91))
      | ~ v1_relat_1(A_91)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_14])).

tff(c_959,plain,(
    ! [A_162] :
      ( r1_tarski(k1_relat_1(A_162),k2_relat_1(k2_funct_1(A_162)))
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v1_relat_1(A_162)
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_307])).

tff(c_970,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_959])).

tff(c_979,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_72,c_64,c_115,c_970])).

tff(c_980,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_979])).

tff(c_983,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_980])).

tff(c_987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_72,c_983])).

tff(c_989,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_979])).

tff(c_30,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k2_funct_1(A_17)) = k6_relat_1(k1_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_135,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_128])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_600,plain,(
    ! [F_141,A_137,B_138,E_142,C_139,D_140] :
      ( k1_partfun1(A_137,B_138,C_139,D_140,E_142,F_141) = k5_relat_1(E_142,F_141)
      | ~ m1_subset_1(F_141,k1_zfmisc_1(k2_zfmisc_1(C_139,D_140)))
      | ~ v1_funct_1(F_141)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(E_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_602,plain,(
    ! [A_137,B_138,E_142] :
      ( k1_partfun1(A_137,B_138,'#skF_2','#skF_3',E_142,'#skF_5') = k5_relat_1(E_142,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(E_142) ) ),
    inference(resolution,[status(thm)],[c_68,c_600])).

tff(c_874,plain,(
    ! [A_159,B_160,E_161] :
      ( k1_partfun1(A_159,B_160,'#skF_2','#skF_3',E_161,'#skF_5') = k5_relat_1(E_161,'#skF_5')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_1(E_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_602])).

tff(c_886,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_874])).

tff(c_896,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_886])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1097,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_66])).

tff(c_54,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] :
      ( m1_subset_1(k1_partfun1(A_33,B_34,C_35,D_36,E_37,F_38),k1_zfmisc_1(k2_zfmisc_1(A_33,D_36)))
      | ~ m1_subset_1(F_38,k1_zfmisc_1(k2_zfmisc_1(C_35,D_36)))
      | ~ v1_funct_1(F_38)
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(E_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1101,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_54])).

tff(c_1105,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1101])).

tff(c_40,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1166,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1105,c_40])).

tff(c_1207,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_1166])).

tff(c_117,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(k2_relat_1(B_56),A_57)
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,(
    ! [B_87,A_88] :
      ( k2_relat_1(B_87) = A_88
      | ~ r1_tarski(A_88,k2_relat_1(B_87))
      | ~ v5_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_277,plain,(
    ! [A_8,B_10] :
      ( k2_relat_1(k5_relat_1(A_8,B_10)) = k2_relat_1(B_10)
      | ~ v5_relat_1(B_10,k2_relat_1(k5_relat_1(A_8,B_10)))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_252])).

tff(c_1228,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_277])).

tff(c_1269,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_115,c_135,c_1207,c_1228])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1315,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_7)) = k9_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1269,c_12])).

tff(c_1575,plain,(
    ! [B_190] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_190)) = k9_relat_1(B_190,'#skF_3')
      | ~ v1_relat_1(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_1315])).

tff(c_1637,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1('#skF_5'))) = k9_relat_1(k2_funct_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1575])).

tff(c_1651,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_72,c_64,c_989,c_18,c_481,c_1637])).

tff(c_314,plain,(
    ! [B_92,A_93] :
      ( k10_relat_1(k2_funct_1(B_92),A_93) = k9_relat_1(B_92,A_93)
      | ~ v2_funct_1(B_92)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,k10_relat_1(B_14,A_13)),A_13)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1075,plain,(
    ! [B_163,A_164] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_163),k9_relat_1(B_163,A_164)),A_164)
      | ~ v1_funct_1(k2_funct_1(B_163))
      | ~ v1_relat_1(k2_funct_1(B_163))
      | ~ v2_funct_1(B_163)
      | ~ v1_funct_1(B_163)
      | ~ v1_relat_1(B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_24])).

tff(c_10698,plain,(
    ! [B_522,A_523] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_522),k2_relat_1(k5_relat_1(A_523,B_522))),k2_relat_1(A_523))
      | ~ v1_funct_1(k2_funct_1(B_522))
      | ~ v1_relat_1(k2_funct_1(B_522))
      | ~ v2_funct_1(B_522)
      | ~ v1_funct_1(B_522)
      | ~ v1_relat_1(B_522)
      | ~ v1_relat_1(B_522)
      | ~ v1_relat_1(A_523) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1075])).

tff(c_10739,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1('#skF_5'),'#skF_3'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_10698])).

tff(c_10780,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_115,c_115,c_72,c_64,c_989,c_1651,c_10739])).

tff(c_10786,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10780])).

tff(c_10789,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_10786])).

tff(c_10793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_72,c_10789])).

tff(c_10794,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10780])).

tff(c_123,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(B_56) = A_57
      | ~ r1_tarski(A_57,k2_relat_1(B_56))
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_10872,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10794,c_123])).

tff(c_10877,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_136,c_10872])).

tff(c_10879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_10877])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n006.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 09:50:52 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.31/4.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.31/4.19  
% 11.31/4.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.31/4.19  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.31/4.19  
% 11.31/4.19  %Foreground sorts:
% 11.31/4.19  
% 11.31/4.19  
% 11.31/4.19  %Background operators:
% 11.31/4.19  
% 11.31/4.19  
% 11.31/4.19  %Foreground operators:
% 11.31/4.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.31/4.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.31/4.19  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.31/4.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.31/4.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.31/4.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.31/4.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.31/4.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.31/4.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.31/4.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.31/4.19  tff('#skF_5', type, '#skF_5': $i).
% 11.31/4.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.31/4.19  tff('#skF_2', type, '#skF_2': $i).
% 11.31/4.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.31/4.19  tff('#skF_3', type, '#skF_3': $i).
% 11.31/4.19  tff('#skF_1', type, '#skF_1': $i).
% 11.31/4.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.31/4.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.31/4.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.31/4.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.31/4.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.31/4.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.31/4.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.31/4.19  tff('#skF_4', type, '#skF_4': $i).
% 11.31/4.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.31/4.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.31/4.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.31/4.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.31/4.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.31/4.19  
% 11.31/4.21  tff(f_167, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 11.31/4.21  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.31/4.21  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.31/4.21  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.31/4.21  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.31/4.21  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.31/4.21  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.31/4.21  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.31/4.21  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 11.31/4.21  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 11.31/4.21  tff(f_145, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.31/4.21  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.31/4.21  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 11.31/4.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.31/4.21  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 11.31/4.21  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 11.31/4.21  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 11.31/4.21  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_217, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.31/4.21  tff(c_225, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_217])).
% 11.31/4.21  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_238, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_225, c_60])).
% 11.31/4.21  tff(c_108, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.31/4.21  tff(c_116, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_108])).
% 11.31/4.21  tff(c_128, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.31/4.21  tff(c_136, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_128])).
% 11.31/4.21  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_115, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_108])).
% 11.31/4.21  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_20, plain, (![A_12]: (v1_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.31/4.21  tff(c_64, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_22, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.31/4.21  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_208, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.31/4.21  tff(c_215, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_208])).
% 11.31/4.21  tff(c_471, plain, (![B_116, A_117, C_118]: (k1_xboole_0=B_116 | k1_relset_1(A_117, B_116, C_118)=A_117 | ~v1_funct_2(C_118, A_117, B_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.31/4.21  tff(c_474, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_471])).
% 11.31/4.21  tff(c_480, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_215, c_474])).
% 11.31/4.21  tff(c_481, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_480])).
% 11.31/4.21  tff(c_18, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.31/4.21  tff(c_301, plain, (![A_91]: (k5_relat_1(A_91, k2_funct_1(A_91))=k6_relat_1(k1_relat_1(A_91)) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.31/4.21  tff(c_14, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k5_relat_1(A_8, B_10)), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.31/4.21  tff(c_307, plain, (![A_91]: (r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_91))), k2_relat_1(k2_funct_1(A_91))) | ~v1_relat_1(k2_funct_1(A_91)) | ~v1_relat_1(A_91) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_301, c_14])).
% 11.31/4.21  tff(c_959, plain, (![A_162]: (r1_tarski(k1_relat_1(A_162), k2_relat_1(k2_funct_1(A_162))) | ~v1_relat_1(k2_funct_1(A_162)) | ~v1_relat_1(A_162) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_307])).
% 11.31/4.21  tff(c_970, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_481, c_959])).
% 11.31/4.21  tff(c_979, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_72, c_64, c_115, c_970])).
% 11.31/4.21  tff(c_980, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_979])).
% 11.31/4.21  tff(c_983, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_980])).
% 11.31/4.21  tff(c_987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_72, c_983])).
% 11.31/4.21  tff(c_989, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_979])).
% 11.31/4.21  tff(c_30, plain, (![A_17]: (k5_relat_1(A_17, k2_funct_1(A_17))=k6_relat_1(k1_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.31/4.21  tff(c_135, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_128])).
% 11.31/4.21  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_600, plain, (![F_141, A_137, B_138, E_142, C_139, D_140]: (k1_partfun1(A_137, B_138, C_139, D_140, E_142, F_141)=k5_relat_1(E_142, F_141) | ~m1_subset_1(F_141, k1_zfmisc_1(k2_zfmisc_1(C_139, D_140))) | ~v1_funct_1(F_141) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(E_142))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.31/4.21  tff(c_602, plain, (![A_137, B_138, E_142]: (k1_partfun1(A_137, B_138, '#skF_2', '#skF_3', E_142, '#skF_5')=k5_relat_1(E_142, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(E_142))), inference(resolution, [status(thm)], [c_68, c_600])).
% 11.31/4.21  tff(c_874, plain, (![A_159, B_160, E_161]: (k1_partfun1(A_159, B_160, '#skF_2', '#skF_3', E_161, '#skF_5')=k5_relat_1(E_161, '#skF_5') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_1(E_161))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_602])).
% 11.31/4.21  tff(c_886, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_874])).
% 11.31/4.21  tff(c_896, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_886])).
% 11.31/4.21  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_167])).
% 11.31/4.21  tff(c_1097, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_896, c_66])).
% 11.31/4.21  tff(c_54, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (m1_subset_1(k1_partfun1(A_33, B_34, C_35, D_36, E_37, F_38), k1_zfmisc_1(k2_zfmisc_1(A_33, D_36))) | ~m1_subset_1(F_38, k1_zfmisc_1(k2_zfmisc_1(C_35, D_36))) | ~v1_funct_1(F_38) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(E_37))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.31/4.21  tff(c_1101, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_896, c_54])).
% 11.31/4.21  tff(c_1105, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1101])).
% 11.31/4.21  tff(c_40, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.31/4.21  tff(c_1166, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1105, c_40])).
% 11.31/4.21  tff(c_1207, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1097, c_1166])).
% 11.31/4.21  tff(c_117, plain, (![B_56, A_57]: (r1_tarski(k2_relat_1(B_56), A_57) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.31/4.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.31/4.21  tff(c_252, plain, (![B_87, A_88]: (k2_relat_1(B_87)=A_88 | ~r1_tarski(A_88, k2_relat_1(B_87)) | ~v5_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_117, c_2])).
% 11.31/4.21  tff(c_277, plain, (![A_8, B_10]: (k2_relat_1(k5_relat_1(A_8, B_10))=k2_relat_1(B_10) | ~v5_relat_1(B_10, k2_relat_1(k5_relat_1(A_8, B_10))) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_252])).
% 11.31/4.21  tff(c_1228, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1207, c_277])).
% 11.31/4.21  tff(c_1269, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_115, c_135, c_1207, c_1228])).
% 11.31/4.21  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.31/4.21  tff(c_1315, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_5', B_7))=k9_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1269, c_12])).
% 11.31/4.21  tff(c_1575, plain, (![B_190]: (k2_relat_1(k5_relat_1('#skF_5', B_190))=k9_relat_1(B_190, '#skF_3') | ~v1_relat_1(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_1315])).
% 11.31/4.21  tff(c_1637, plain, (k2_relat_1(k6_relat_1(k1_relat_1('#skF_5')))=k9_relat_1(k2_funct_1('#skF_5'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1575])).
% 11.31/4.21  tff(c_1651, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_72, c_64, c_989, c_18, c_481, c_1637])).
% 11.31/4.21  tff(c_314, plain, (![B_92, A_93]: (k10_relat_1(k2_funct_1(B_92), A_93)=k9_relat_1(B_92, A_93) | ~v2_funct_1(B_92) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.31/4.21  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, k10_relat_1(B_14, A_13)), A_13) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.31/4.21  tff(c_1075, plain, (![B_163, A_164]: (r1_tarski(k9_relat_1(k2_funct_1(B_163), k9_relat_1(B_163, A_164)), A_164) | ~v1_funct_1(k2_funct_1(B_163)) | ~v1_relat_1(k2_funct_1(B_163)) | ~v2_funct_1(B_163) | ~v1_funct_1(B_163) | ~v1_relat_1(B_163))), inference(superposition, [status(thm), theory('equality')], [c_314, c_24])).
% 11.31/4.21  tff(c_10698, plain, (![B_522, A_523]: (r1_tarski(k9_relat_1(k2_funct_1(B_522), k2_relat_1(k5_relat_1(A_523, B_522))), k2_relat_1(A_523)) | ~v1_funct_1(k2_funct_1(B_522)) | ~v1_relat_1(k2_funct_1(B_522)) | ~v2_funct_1(B_522) | ~v1_funct_1(B_522) | ~v1_relat_1(B_522) | ~v1_relat_1(B_522) | ~v1_relat_1(A_523))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1075])).
% 11.31/4.21  tff(c_10739, plain, (r1_tarski(k9_relat_1(k2_funct_1('#skF_5'), '#skF_3'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1207, c_10698])).
% 11.31/4.21  tff(c_10780, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_115, c_115, c_72, c_64, c_989, c_1651, c_10739])).
% 11.31/4.21  tff(c_10786, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_10780])).
% 11.31/4.21  tff(c_10789, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_10786])).
% 11.31/4.21  tff(c_10793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_72, c_10789])).
% 11.31/4.21  tff(c_10794, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10780])).
% 11.31/4.21  tff(c_123, plain, (![B_56, A_57]: (k2_relat_1(B_56)=A_57 | ~r1_tarski(A_57, k2_relat_1(B_56)) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_117, c_2])).
% 11.31/4.21  tff(c_10872, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10794, c_123])).
% 11.31/4.21  tff(c_10877, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_136, c_10872])).
% 11.31/4.21  tff(c_10879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_10877])).
% 11.31/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.31/4.21  
% 11.31/4.21  Inference rules
% 11.31/4.21  ----------------------
% 11.31/4.21  #Ref     : 0
% 11.31/4.21  #Sup     : 2260
% 11.31/4.21  #Fact    : 0
% 11.31/4.21  #Define  : 0
% 11.31/4.21  #Split   : 22
% 11.31/4.21  #Chain   : 0
% 11.31/4.21  #Close   : 0
% 11.31/4.21  
% 11.31/4.21  Ordering : KBO
% 11.31/4.21  
% 11.31/4.21  Simplification rules
% 11.31/4.21  ----------------------
% 11.31/4.21  #Subsume      : 254
% 11.31/4.21  #Demod        : 3246
% 11.31/4.21  #Tautology    : 549
% 11.31/4.21  #SimpNegUnit  : 74
% 11.31/4.21  #BackRed      : 299
% 11.31/4.21  
% 11.31/4.21  #Partial instantiations: 0
% 11.31/4.21  #Strategies tried      : 1
% 11.31/4.21  
% 11.31/4.21  Timing (in seconds)
% 11.31/4.21  ----------------------
% 11.31/4.22  Preprocessing        : 0.36
% 11.31/4.22  Parsing              : 0.19
% 11.31/4.22  CNF conversion       : 0.02
% 11.31/4.22  Main loop            : 3.06
% 11.31/4.22  Inferencing          : 0.84
% 11.31/4.22  Reduction            : 1.34
% 11.31/4.22  Demodulation         : 1.02
% 11.31/4.22  BG Simplification    : 0.08
% 11.31/4.22  Subsumption          : 0.59
% 11.31/4.22  Abstraction          : 0.11
% 11.31/4.22  MUC search           : 0.00
% 11.31/4.22  Cooper               : 0.00
% 11.31/4.22  Total                : 3.46
% 11.31/4.22  Index Insertion      : 0.00
% 11.31/4.22  Index Deletion       : 0.00
% 11.31/4.22  Index Matching       : 0.00
% 11.31/4.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
