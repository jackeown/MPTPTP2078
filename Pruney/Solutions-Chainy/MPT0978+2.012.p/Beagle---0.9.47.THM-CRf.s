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
% DateTime   : Thu Dec  3 10:11:53 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 155 expanded)
%              Number of leaves         :   41 (  72 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 391 expanded)
%              Number of equality atoms :   33 (  74 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_127,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_109,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_413,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_426,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_413])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_440,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_42])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_89,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_98,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_98])).

tff(c_40,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_57,plain,(
    ! [A_15] : k2_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1191,plain,(
    ! [F_154,C_155,B_152,D_151,E_156,A_153] :
      ( m1_subset_1(k1_partfun1(A_153,B_152,C_155,D_151,E_156,F_154),k1_zfmisc_1(k2_zfmisc_1(A_153,D_151)))
      | ~ m1_subset_1(F_154,k1_zfmisc_1(k2_zfmisc_1(C_155,D_151)))
      | ~ v1_funct_1(F_154)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152)))
      | ~ v1_funct_1(E_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_511,plain,(
    ! [D_96,C_97,A_98,B_99] :
      ( D_96 = C_97
      | ~ r2_relset_1(A_98,B_99,C_97,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_519,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_44,c_511])).

tff(c_534,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_519])).

tff(c_591,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_1204,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1191,c_591])).

tff(c_1226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_56,c_52,c_1204])).

tff(c_1227,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_1554,plain,(
    ! [C_176,A_174,F_177,B_179,D_178,E_175] :
      ( k1_partfun1(A_174,B_179,C_176,D_178,E_175,F_177) = k5_relat_1(E_175,F_177)
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(C_176,D_178)))
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_174,B_179)))
      | ~ v1_funct_1(E_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1560,plain,(
    ! [A_174,B_179,E_175] :
      ( k1_partfun1(A_174,B_179,'#skF_1','#skF_2',E_175,'#skF_3') = k5_relat_1(E_175,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_174,B_179)))
      | ~ v1_funct_1(E_175) ) ),
    inference(resolution,[status(thm)],[c_52,c_1554])).

tff(c_1957,plain,(
    ! [A_205,B_206,E_207] :
      ( k1_partfun1(A_205,B_206,'#skF_1','#skF_2',E_207,'#skF_3') = k5_relat_1(E_207,'#skF_3')
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206)))
      | ~ v1_funct_1(E_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1560])).

tff(c_1972,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1957])).

tff(c_1986,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1227,c_1972])).

tff(c_123,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_135,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_123])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_182,plain,(
    ! [A_69,B_70] :
      ( k8_relat_1(A_69,B_70) = B_70
      | ~ r1_tarski(k2_relat_1(B_70),A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_236,plain,(
    ! [A_75,B_76] :
      ( k8_relat_1(A_75,B_76) = B_76
      | ~ v5_relat_1(B_76,A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_182])).

tff(c_248,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_236])).

tff(c_261,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_248])).

tff(c_362,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_85,B_86)),k2_relat_1(B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_relat_1(k8_relat_1(A_8,B_9)) = A_8
      | ~ r1_tarski(A_8,k2_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_378,plain,(
    ! [A_85,B_86] :
      ( k2_relat_1(k8_relat_1(k2_relat_1(k5_relat_1(A_85,B_86)),B_86)) = k2_relat_1(k5_relat_1(A_85,B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_362,c_10])).

tff(c_1996,plain,
    ( k2_relat_1(k8_relat_1(k2_relat_1(k6_partfun1('#skF_2')),'#skF_3')) = k2_relat_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1986,c_378])).

tff(c_2008,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_107,c_57,c_1986,c_261,c_57,c_1996])).

tff(c_2010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_2008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:34:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.78  
% 4.32/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.78  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.32/1.78  
% 4.32/1.78  %Foreground sorts:
% 4.32/1.78  
% 4.32/1.78  
% 4.32/1.78  %Background operators:
% 4.32/1.78  
% 4.32/1.78  
% 4.32/1.78  %Foreground operators:
% 4.32/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.32/1.78  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.32/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.78  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.32/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.32/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.32/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.32/1.78  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.32/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.32/1.78  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.32/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.32/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.32/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.32/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.32/1.78  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.32/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.32/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.32/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.32/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.32/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.32/1.78  
% 4.39/1.80  tff(f_127, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.39/1.80  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.39/1.80  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.39/1.80  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.39/1.80  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.39/1.80  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.39/1.80  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.39/1.80  tff(f_97, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.39/1.80  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.39/1.80  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.39/1.80  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.39/1.80  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.39/1.80  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 4.39/1.80  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 4.39/1.80  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 4.39/1.80  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.39/1.80  tff(c_413, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.39/1.80  tff(c_426, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_413])).
% 4.39/1.80  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.39/1.80  tff(c_440, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_426, c_42])).
% 4.39/1.80  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.39/1.80  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.39/1.80  tff(c_89, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.80  tff(c_95, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_89])).
% 4.39/1.80  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_95])).
% 4.39/1.80  tff(c_98, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_89])).
% 4.39/1.80  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_98])).
% 4.39/1.80  tff(c_40, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.39/1.80  tff(c_18, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.39/1.80  tff(c_57, plain, (![A_15]: (k2_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18])).
% 4.39/1.80  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.39/1.80  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.39/1.80  tff(c_1191, plain, (![F_154, C_155, B_152, D_151, E_156, A_153]: (m1_subset_1(k1_partfun1(A_153, B_152, C_155, D_151, E_156, F_154), k1_zfmisc_1(k2_zfmisc_1(A_153, D_151))) | ~m1_subset_1(F_154, k1_zfmisc_1(k2_zfmisc_1(C_155, D_151))) | ~v1_funct_1(F_154) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))) | ~v1_funct_1(E_156))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.39/1.80  tff(c_36, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.39/1.80  tff(c_44, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.39/1.80  tff(c_511, plain, (![D_96, C_97, A_98, B_99]: (D_96=C_97 | ~r2_relset_1(A_98, B_99, C_97, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.39/1.80  tff(c_519, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_44, c_511])).
% 4.39/1.80  tff(c_534, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_519])).
% 4.39/1.80  tff(c_591, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_534])).
% 4.39/1.80  tff(c_1204, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1191, c_591])).
% 4.39/1.80  tff(c_1226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_56, c_52, c_1204])).
% 4.39/1.80  tff(c_1227, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_534])).
% 4.39/1.80  tff(c_1554, plain, (![C_176, A_174, F_177, B_179, D_178, E_175]: (k1_partfun1(A_174, B_179, C_176, D_178, E_175, F_177)=k5_relat_1(E_175, F_177) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(C_176, D_178))) | ~v1_funct_1(F_177) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_174, B_179))) | ~v1_funct_1(E_175))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.39/1.80  tff(c_1560, plain, (![A_174, B_179, E_175]: (k1_partfun1(A_174, B_179, '#skF_1', '#skF_2', E_175, '#skF_3')=k5_relat_1(E_175, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_174, B_179))) | ~v1_funct_1(E_175))), inference(resolution, [status(thm)], [c_52, c_1554])).
% 4.39/1.80  tff(c_1957, plain, (![A_205, B_206, E_207]: (k1_partfun1(A_205, B_206, '#skF_1', '#skF_2', E_207, '#skF_3')=k5_relat_1(E_207, '#skF_3') | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))) | ~v1_funct_1(E_207))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1560])).
% 4.39/1.80  tff(c_1972, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1957])).
% 4.39/1.80  tff(c_1986, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1227, c_1972])).
% 4.39/1.80  tff(c_123, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.39/1.80  tff(c_135, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_123])).
% 4.39/1.80  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.39/1.80  tff(c_182, plain, (![A_69, B_70]: (k8_relat_1(A_69, B_70)=B_70 | ~r1_tarski(k2_relat_1(B_70), A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.39/1.80  tff(c_236, plain, (![A_75, B_76]: (k8_relat_1(A_75, B_76)=B_76 | ~v5_relat_1(B_76, A_75) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_6, c_182])).
% 4.39/1.80  tff(c_248, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_236])).
% 4.39/1.80  tff(c_261, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_248])).
% 4.39/1.80  tff(c_362, plain, (![A_85, B_86]: (r1_tarski(k2_relat_1(k5_relat_1(A_85, B_86)), k2_relat_1(B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.39/1.80  tff(c_10, plain, (![A_8, B_9]: (k2_relat_1(k8_relat_1(A_8, B_9))=A_8 | ~r1_tarski(A_8, k2_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.39/1.80  tff(c_378, plain, (![A_85, B_86]: (k2_relat_1(k8_relat_1(k2_relat_1(k5_relat_1(A_85, B_86)), B_86))=k2_relat_1(k5_relat_1(A_85, B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_362, c_10])).
% 4.39/1.80  tff(c_1996, plain, (k2_relat_1(k8_relat_1(k2_relat_1(k6_partfun1('#skF_2')), '#skF_3'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1986, c_378])).
% 4.39/1.80  tff(c_2008, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_107, c_57, c_1986, c_261, c_57, c_1996])).
% 4.39/1.80  tff(c_2010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_2008])).
% 4.39/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.80  
% 4.39/1.80  Inference rules
% 4.39/1.80  ----------------------
% 4.39/1.80  #Ref     : 0
% 4.39/1.80  #Sup     : 451
% 4.39/1.80  #Fact    : 0
% 4.39/1.80  #Define  : 0
% 4.39/1.80  #Split   : 1
% 4.39/1.80  #Chain   : 0
% 4.39/1.80  #Close   : 0
% 4.39/1.80  
% 4.39/1.80  Ordering : KBO
% 4.39/1.80  
% 4.39/1.80  Simplification rules
% 4.39/1.80  ----------------------
% 4.39/1.80  #Subsume      : 28
% 4.39/1.80  #Demod        : 347
% 4.39/1.80  #Tautology    : 138
% 4.39/1.80  #SimpNegUnit  : 1
% 4.39/1.80  #BackRed      : 4
% 4.39/1.80  
% 4.39/1.80  #Partial instantiations: 0
% 4.39/1.80  #Strategies tried      : 1
% 4.39/1.80  
% 4.39/1.80  Timing (in seconds)
% 4.39/1.80  ----------------------
% 4.39/1.80  Preprocessing        : 0.36
% 4.39/1.80  Parsing              : 0.19
% 4.39/1.80  CNF conversion       : 0.03
% 4.39/1.80  Main loop            : 0.60
% 4.39/1.80  Inferencing          : 0.21
% 4.39/1.80  Reduction            : 0.21
% 4.39/1.80  Demodulation         : 0.15
% 4.39/1.80  BG Simplification    : 0.03
% 4.39/1.80  Subsumption          : 0.11
% 4.39/1.80  Abstraction          : 0.03
% 4.39/1.80  MUC search           : 0.00
% 4.39/1.80  Cooper               : 0.00
% 4.39/1.80  Total                : 1.01
% 4.39/1.80  Index Insertion      : 0.00
% 4.39/1.80  Index Deletion       : 0.00
% 4.39/1.80  Index Matching       : 0.00
% 4.39/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
