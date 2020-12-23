%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:52 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 179 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 526 expanded)
%              Number of equality atoms :   39 (  85 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_91,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

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

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_258,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_275,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_258])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_317,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_46])).

tff(c_94,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_178,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_191,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_178])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_510,plain,(
    ! [C_110,A_108,B_107,E_111,F_109,D_106] :
      ( k1_partfun1(A_108,B_107,C_110,D_106,E_111,F_109) = k5_relat_1(E_111,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_110,D_106)))
      | ~ v1_funct_1(F_109)
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_1(E_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_518,plain,(
    ! [A_108,B_107,E_111] :
      ( k1_partfun1(A_108,B_107,'#skF_1','#skF_2',E_111,'#skF_3') = k5_relat_1(E_111,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_1(E_111) ) ),
    inference(resolution,[status(thm)],[c_56,c_510])).

tff(c_539,plain,(
    ! [A_114,B_115,E_116] :
      ( k1_partfun1(A_114,B_115,'#skF_1','#skF_2',E_116,'#skF_3') = k5_relat_1(E_116,'#skF_3')
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_1(E_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_518])).

tff(c_548,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_539])).

tff(c_556,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_548])).

tff(c_34,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_289,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r2_relset_1(A_79,B_80,C_78,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_299,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_48,c_289])).

tff(c_316,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_299])).

tff(c_341,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_561,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_341])).

tff(c_577,plain,(
    ! [D_122,B_119,A_120,F_121,C_117,E_118] :
      ( m1_subset_1(k1_partfun1(A_120,B_119,C_117,D_122,E_118,F_121),k1_zfmisc_1(k2_zfmisc_1(A_120,D_122)))
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_117,D_122)))
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_610,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_577])).

tff(c_624,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_60,c_56,c_610])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_561,c_624])).

tff(c_627,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_771,plain,(
    ! [B_143,D_142,F_145,A_144,E_147,C_146] :
      ( k1_partfun1(A_144,B_143,C_146,D_142,E_147,F_145) = k5_relat_1(E_147,F_145)
      | ~ m1_subset_1(F_145,k1_zfmisc_1(k2_zfmisc_1(C_146,D_142)))
      | ~ v1_funct_1(F_145)
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_1(E_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_779,plain,(
    ! [A_144,B_143,E_147] :
      ( k1_partfun1(A_144,B_143,'#skF_1','#skF_2',E_147,'#skF_3') = k5_relat_1(E_147,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_1(E_147) ) ),
    inference(resolution,[status(thm)],[c_56,c_771])).

tff(c_872,plain,(
    ! [A_161,B_162,E_163] :
      ( k1_partfun1(A_161,B_162,'#skF_1','#skF_2',E_163,'#skF_3') = k5_relat_1(E_163,'#skF_3')
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_funct_1(E_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_779])).

tff(c_884,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_872])).

tff(c_893,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_627,c_884])).

tff(c_40,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33))))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1354,plain,(
    ! [A_190,B_191,A_192,E_193] :
      ( k1_partfun1(A_190,B_191,k1_relat_1(A_192),k2_relat_1(A_192),E_193,A_192) = k5_relat_1(E_193,A_192)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(E_193)
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_40,c_771])).

tff(c_1370,plain,(
    ! [A_192] :
      ( k1_partfun1('#skF_2','#skF_1',k1_relat_1(A_192),k2_relat_1(A_192),'#skF_4',A_192) = k5_relat_1('#skF_4',A_192)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_50,c_1354])).

tff(c_1390,plain,(
    ! [A_192] :
      ( k1_partfun1('#skF_2','#skF_1',k1_relat_1(A_192),k2_relat_1(A_192),'#skF_4',A_192) = k5_relat_1('#skF_4',A_192)
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1370])).

tff(c_833,plain,(
    ! [C_155,D_160,A_158,F_159,E_156,B_157] :
      ( m1_subset_1(k1_partfun1(A_158,B_157,C_155,D_160,E_156,F_159),k1_zfmisc_1(k2_zfmisc_1(A_158,D_160)))
      | ~ m1_subset_1(F_159,k1_zfmisc_1(k2_zfmisc_1(C_155,D_160)))
      | ~ v1_funct_1(F_159)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157)))
      | ~ v1_funct_1(E_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [C_11,B_10,A_9] :
      ( v5_relat_1(C_11,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1640,plain,(
    ! [C_210,D_212,F_209,B_213,A_211,E_214] :
      ( v5_relat_1(k1_partfun1(A_211,B_213,C_210,D_212,E_214,F_209),D_212)
      | ~ m1_subset_1(F_209,k1_zfmisc_1(k2_zfmisc_1(C_210,D_212)))
      | ~ v1_funct_1(F_209)
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_211,B_213)))
      | ~ v1_funct_1(E_214) ) ),
    inference(resolution,[status(thm)],[c_833,c_18])).

tff(c_4478,plain,(
    ! [A_350,B_351,A_352,E_353] :
      ( v5_relat_1(k1_partfun1(A_350,B_351,k1_relat_1(A_352),k2_relat_1(A_352),E_353,A_352),k2_relat_1(A_352))
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351)))
      | ~ v1_funct_1(E_353)
      | ~ v1_funct_1(A_352)
      | ~ v1_relat_1(A_352) ) ),
    inference(resolution,[status(thm)],[c_40,c_1640])).

tff(c_4489,plain,(
    ! [A_192] :
      ( v5_relat_1(k5_relat_1('#skF_4',A_192),k2_relat_1(A_192))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192)
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_4478])).

tff(c_4515,plain,(
    ! [A_354] :
      ( v5_relat_1(k5_relat_1('#skF_4',A_354),k2_relat_1(A_354))
      | ~ v1_funct_1(A_354)
      | ~ v1_relat_1(A_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_4489])).

tff(c_4520,plain,
    ( v5_relat_1(k6_partfun1('#skF_2'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_4515])).

tff(c_4526,plain,(
    v5_relat_1(k6_partfun1('#skF_2'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_60,c_4520])).

tff(c_104,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_34,c_94])).

tff(c_38,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61,plain,(
    ! [A_5] : k2_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(k2_relat_1(B_47),A_48)
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_635,plain,(
    ! [B_123,A_124] :
      ( k2_relat_1(B_123) = A_124
      | ~ r1_tarski(A_124,k2_relat_1(B_123))
      | ~ v5_relat_1(B_123,A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_672,plain,(
    ! [B_128,B_127] :
      ( k2_relat_1(B_128) = k2_relat_1(B_127)
      | ~ v5_relat_1(B_128,k2_relat_1(B_127))
      | ~ v1_relat_1(B_128)
      | ~ v5_relat_1(B_127,k2_relat_1(B_128))
      | ~ v1_relat_1(B_127) ) ),
    inference(resolution,[status(thm)],[c_10,c_635])).

tff(c_682,plain,(
    ! [A_5,B_128] :
      ( k2_relat_1(k6_partfun1(A_5)) = k2_relat_1(B_128)
      | ~ v5_relat_1(B_128,A_5)
      | ~ v1_relat_1(B_128)
      | ~ v5_relat_1(k6_partfun1(A_5),k2_relat_1(B_128))
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_672])).

tff(c_692,plain,(
    ! [B_128,A_5] :
      ( k2_relat_1(B_128) = A_5
      | ~ v5_relat_1(B_128,A_5)
      | ~ v1_relat_1(B_128)
      | ~ v5_relat_1(k6_partfun1(A_5),k2_relat_1(B_128)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_61,c_682])).

tff(c_4533,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4526,c_692])).

tff(c_4547,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_191,c_4533])).

tff(c_4549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_4547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.39/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.62  
% 7.39/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.63  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.39/2.63  
% 7.39/2.63  %Foreground sorts:
% 7.39/2.63  
% 7.39/2.63  
% 7.39/2.63  %Background operators:
% 7.39/2.63  
% 7.39/2.63  
% 7.39/2.63  %Foreground operators:
% 7.39/2.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.39/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.39/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.39/2.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.39/2.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.39/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.39/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.39/2.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.39/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.39/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.39/2.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.39/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.39/2.63  tff('#skF_1', type, '#skF_1': $i).
% 7.39/2.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.39/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.39/2.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.39/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.39/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.39/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.39/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.39/2.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.39/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.39/2.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.39/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.39/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.39/2.63  
% 7.39/2.65  tff(f_119, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.39/2.65  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.39/2.65  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.39/2.65  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.39/2.65  tff(f_89, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.39/2.65  tff(f_79, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.39/2.65  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.39/2.65  tff(f_75, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.39/2.65  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.39/2.65  tff(f_91, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.39/2.65  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.39/2.65  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.39/2.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.39/2.65  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.39/2.65  tff(c_258, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.39/2.65  tff(c_275, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_258])).
% 7.39/2.65  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.39/2.65  tff(c_317, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_46])).
% 7.39/2.65  tff(c_94, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.39/2.65  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_94])).
% 7.39/2.65  tff(c_178, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.39/2.65  tff(c_191, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_178])).
% 7.39/2.65  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.39/2.65  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.39/2.65  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.39/2.65  tff(c_510, plain, (![C_110, A_108, B_107, E_111, F_109, D_106]: (k1_partfun1(A_108, B_107, C_110, D_106, E_111, F_109)=k5_relat_1(E_111, F_109) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(C_110, D_106))) | ~v1_funct_1(F_109) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_1(E_111))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.39/2.65  tff(c_518, plain, (![A_108, B_107, E_111]: (k1_partfun1(A_108, B_107, '#skF_1', '#skF_2', E_111, '#skF_3')=k5_relat_1(E_111, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_1(E_111))), inference(resolution, [status(thm)], [c_56, c_510])).
% 7.39/2.65  tff(c_539, plain, (![A_114, B_115, E_116]: (k1_partfun1(A_114, B_115, '#skF_1', '#skF_2', E_116, '#skF_3')=k5_relat_1(E_116, '#skF_3') | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_1(E_116))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_518])).
% 7.39/2.65  tff(c_548, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_539])).
% 7.39/2.65  tff(c_556, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_548])).
% 7.39/2.65  tff(c_34, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.39/2.65  tff(c_48, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.39/2.65  tff(c_289, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r2_relset_1(A_79, B_80, C_78, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.39/2.65  tff(c_299, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_48, c_289])).
% 7.39/2.65  tff(c_316, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_299])).
% 7.39/2.65  tff(c_341, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_316])).
% 7.39/2.65  tff(c_561, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_341])).
% 7.39/2.65  tff(c_577, plain, (![D_122, B_119, A_120, F_121, C_117, E_118]: (m1_subset_1(k1_partfun1(A_120, B_119, C_117, D_122, E_118, F_121), k1_zfmisc_1(k2_zfmisc_1(A_120, D_122))) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_117, D_122))) | ~v1_funct_1(F_121) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.39/2.65  tff(c_610, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_556, c_577])).
% 7.39/2.65  tff(c_624, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_60, c_56, c_610])).
% 7.39/2.65  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_561, c_624])).
% 7.39/2.65  tff(c_627, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_316])).
% 7.39/2.65  tff(c_771, plain, (![B_143, D_142, F_145, A_144, E_147, C_146]: (k1_partfun1(A_144, B_143, C_146, D_142, E_147, F_145)=k5_relat_1(E_147, F_145) | ~m1_subset_1(F_145, k1_zfmisc_1(k2_zfmisc_1(C_146, D_142))) | ~v1_funct_1(F_145) | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_1(E_147))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.39/2.65  tff(c_779, plain, (![A_144, B_143, E_147]: (k1_partfun1(A_144, B_143, '#skF_1', '#skF_2', E_147, '#skF_3')=k5_relat_1(E_147, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_1(E_147))), inference(resolution, [status(thm)], [c_56, c_771])).
% 7.39/2.65  tff(c_872, plain, (![A_161, B_162, E_163]: (k1_partfun1(A_161, B_162, '#skF_1', '#skF_2', E_163, '#skF_3')=k5_relat_1(E_163, '#skF_3') | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_funct_1(E_163))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_779])).
% 7.39/2.65  tff(c_884, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_872])).
% 7.39/2.65  tff(c_893, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_627, c_884])).
% 7.39/2.65  tff(c_40, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33)))) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.39/2.65  tff(c_1354, plain, (![A_190, B_191, A_192, E_193]: (k1_partfun1(A_190, B_191, k1_relat_1(A_192), k2_relat_1(A_192), E_193, A_192)=k5_relat_1(E_193, A_192) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(E_193) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(resolution, [status(thm)], [c_40, c_771])).
% 7.39/2.65  tff(c_1370, plain, (![A_192]: (k1_partfun1('#skF_2', '#skF_1', k1_relat_1(A_192), k2_relat_1(A_192), '#skF_4', A_192)=k5_relat_1('#skF_4', A_192) | ~v1_funct_1('#skF_4') | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(resolution, [status(thm)], [c_50, c_1354])).
% 7.39/2.65  tff(c_1390, plain, (![A_192]: (k1_partfun1('#skF_2', '#skF_1', k1_relat_1(A_192), k2_relat_1(A_192), '#skF_4', A_192)=k5_relat_1('#skF_4', A_192) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1370])).
% 7.39/2.65  tff(c_833, plain, (![C_155, D_160, A_158, F_159, E_156, B_157]: (m1_subset_1(k1_partfun1(A_158, B_157, C_155, D_160, E_156, F_159), k1_zfmisc_1(k2_zfmisc_1(A_158, D_160))) | ~m1_subset_1(F_159, k1_zfmisc_1(k2_zfmisc_1(C_155, D_160))) | ~v1_funct_1(F_159) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))) | ~v1_funct_1(E_156))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.39/2.65  tff(c_18, plain, (![C_11, B_10, A_9]: (v5_relat_1(C_11, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.39/2.65  tff(c_1640, plain, (![C_210, D_212, F_209, B_213, A_211, E_214]: (v5_relat_1(k1_partfun1(A_211, B_213, C_210, D_212, E_214, F_209), D_212) | ~m1_subset_1(F_209, k1_zfmisc_1(k2_zfmisc_1(C_210, D_212))) | ~v1_funct_1(F_209) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_211, B_213))) | ~v1_funct_1(E_214))), inference(resolution, [status(thm)], [c_833, c_18])).
% 7.39/2.65  tff(c_4478, plain, (![A_350, B_351, A_352, E_353]: (v5_relat_1(k1_partfun1(A_350, B_351, k1_relat_1(A_352), k2_relat_1(A_352), E_353, A_352), k2_relat_1(A_352)) | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(A_350, B_351))) | ~v1_funct_1(E_353) | ~v1_funct_1(A_352) | ~v1_relat_1(A_352))), inference(resolution, [status(thm)], [c_40, c_1640])).
% 7.39/2.65  tff(c_4489, plain, (![A_192]: (v5_relat_1(k5_relat_1('#skF_4', A_192), k2_relat_1(A_192)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~v1_funct_1(A_192) | ~v1_relat_1(A_192) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(superposition, [status(thm), theory('equality')], [c_1390, c_4478])).
% 7.39/2.65  tff(c_4515, plain, (![A_354]: (v5_relat_1(k5_relat_1('#skF_4', A_354), k2_relat_1(A_354)) | ~v1_funct_1(A_354) | ~v1_relat_1(A_354))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_4489])).
% 7.39/2.65  tff(c_4520, plain, (v5_relat_1(k6_partfun1('#skF_2'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_893, c_4515])).
% 7.39/2.65  tff(c_4526, plain, (v5_relat_1(k6_partfun1('#skF_2'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_60, c_4520])).
% 7.39/2.65  tff(c_104, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_34, c_94])).
% 7.39/2.65  tff(c_38, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.39/2.65  tff(c_14, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.39/2.65  tff(c_61, plain, (![A_5]: (k2_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 7.39/2.65  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.39/2.65  tff(c_115, plain, (![B_47, A_48]: (r1_tarski(k2_relat_1(B_47), A_48) | ~v5_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.39/2.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.39/2.65  tff(c_635, plain, (![B_123, A_124]: (k2_relat_1(B_123)=A_124 | ~r1_tarski(A_124, k2_relat_1(B_123)) | ~v5_relat_1(B_123, A_124) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_115, c_2])).
% 7.39/2.65  tff(c_672, plain, (![B_128, B_127]: (k2_relat_1(B_128)=k2_relat_1(B_127) | ~v5_relat_1(B_128, k2_relat_1(B_127)) | ~v1_relat_1(B_128) | ~v5_relat_1(B_127, k2_relat_1(B_128)) | ~v1_relat_1(B_127))), inference(resolution, [status(thm)], [c_10, c_635])).
% 7.39/2.65  tff(c_682, plain, (![A_5, B_128]: (k2_relat_1(k6_partfun1(A_5))=k2_relat_1(B_128) | ~v5_relat_1(B_128, A_5) | ~v1_relat_1(B_128) | ~v5_relat_1(k6_partfun1(A_5), k2_relat_1(B_128)) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_672])).
% 7.39/2.65  tff(c_692, plain, (![B_128, A_5]: (k2_relat_1(B_128)=A_5 | ~v5_relat_1(B_128, A_5) | ~v1_relat_1(B_128) | ~v5_relat_1(k6_partfun1(A_5), k2_relat_1(B_128)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_61, c_682])).
% 7.39/2.65  tff(c_4533, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4526, c_692])).
% 7.39/2.65  tff(c_4547, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_191, c_4533])).
% 7.39/2.65  tff(c_4549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_317, c_4547])).
% 7.39/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.65  
% 7.39/2.65  Inference rules
% 7.39/2.65  ----------------------
% 7.39/2.65  #Ref     : 0
% 7.39/2.65  #Sup     : 931
% 7.39/2.65  #Fact    : 0
% 7.39/2.65  #Define  : 0
% 7.39/2.65  #Split   : 1
% 7.39/2.65  #Chain   : 0
% 7.39/2.65  #Close   : 0
% 7.39/2.65  
% 7.39/2.65  Ordering : KBO
% 7.39/2.65  
% 7.39/2.65  Simplification rules
% 7.39/2.65  ----------------------
% 7.39/2.65  #Subsume      : 46
% 7.39/2.65  #Demod        : 1292
% 7.39/2.65  #Tautology    : 192
% 7.39/2.65  #SimpNegUnit  : 3
% 7.39/2.65  #BackRed      : 19
% 7.39/2.65  
% 7.39/2.65  #Partial instantiations: 0
% 7.39/2.65  #Strategies tried      : 1
% 7.39/2.65  
% 7.39/2.65  Timing (in seconds)
% 7.39/2.65  ----------------------
% 7.39/2.65  Preprocessing        : 0.32
% 7.39/2.65  Parsing              : 0.18
% 7.39/2.65  CNF conversion       : 0.02
% 7.39/2.65  Main loop            : 1.55
% 7.39/2.65  Inferencing          : 0.51
% 7.39/2.65  Reduction            : 0.64
% 7.39/2.65  Demodulation         : 0.51
% 7.39/2.65  BG Simplification    : 0.04
% 7.39/2.65  Subsumption          : 0.26
% 7.39/2.65  Abstraction          : 0.06
% 7.39/2.65  MUC search           : 0.00
% 7.39/2.65  Cooper               : 0.00
% 7.39/2.66  Total                : 1.92
% 7.39/2.66  Index Insertion      : 0.00
% 7.39/2.66  Index Deletion       : 0.00
% 7.39/2.66  Index Matching       : 0.00
% 7.39/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
