%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:48 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 120 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :    6
%              Number of atoms          :  114 ( 198 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_86,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_51,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_57])).

tff(c_327,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( r2_relset_1(A_113,B_114,C_115,C_115)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_339,plain,(
    ! [C_120] :
      ( r2_relset_1('#skF_1','#skF_2',C_120,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_327])).

tff(c_342,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_339])).

tff(c_224,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_232,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_224])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_264,plain,(
    ! [A_102,B_103] :
      ( k8_relat_1(A_102,B_103) = B_103
      | ~ r1_tarski(k2_relat_1(B_103),A_102)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_269,plain,(
    ! [A_104,B_105] :
      ( k8_relat_1(A_104,B_105) = B_105
      | ~ v5_relat_1(B_105,A_104)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_10,c_264])).

tff(c_275,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_232,c_269])).

tff(c_281,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_275])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = k8_relat_1(A_10,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_partfun1(A_10)) = k8_relat_1(A_10,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_30,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_343,plain,(
    ! [C_121,A_124,D_126,E_122,B_123,F_125] :
      ( k4_relset_1(A_124,B_123,C_121,D_126,E_122,F_125) = k5_relat_1(E_122,F_125)
      | ~ m1_subset_1(F_125,k1_zfmisc_1(k2_zfmisc_1(C_121,D_126)))
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_378,plain,(
    ! [A_131,B_132,A_133,E_134] :
      ( k4_relset_1(A_131,B_132,A_133,A_133,E_134,k6_partfun1(A_133)) = k5_relat_1(E_134,k6_partfun1(A_133))
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(resolution,[status(thm)],[c_30,c_343])).

tff(c_384,plain,(
    ! [A_133] : k4_relset_1('#skF_1','#skF_2',A_133,A_133,'#skF_3',k6_partfun1(A_133)) = k5_relat_1('#skF_3',k6_partfun1(A_133)) ),
    inference(resolution,[status(thm)],[c_36,c_378])).

tff(c_77,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_170,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( r2_relset_1(A_68,B_69,C_70,C_70)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_182,plain,(
    ! [C_75] :
      ( r2_relset_1('#skF_1','#skF_2',C_75,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_170])).

tff(c_185,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_182])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,(
    ! [A_62,B_63] :
      ( k5_relat_1(k6_partfun1(A_62),B_63) = B_63
      | ~ r1_tarski(k1_relat_1(B_63),A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_142,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_186,plain,(
    ! [D_81,B_78,F_80,E_77,C_76,A_79] :
      ( k4_relset_1(A_79,B_78,C_76,D_81,E_77,F_80) = k5_relat_1(E_77,F_80)
      | ~ m1_subset_1(F_80,k1_zfmisc_1(k2_zfmisc_1(C_76,D_81)))
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_193,plain,(
    ! [A_82,B_83,E_84] :
      ( k4_relset_1(A_82,B_83,'#skF_1','#skF_2',E_84,'#skF_3') = k5_relat_1(E_84,'#skF_3')
      | ~ m1_subset_1(E_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(resolution,[status(thm)],[c_36,c_186])).

tff(c_200,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_34,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_206,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_66])).

tff(c_218,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_206])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_85,c_185,c_218])).

tff(c_222,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_385,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_222])).

tff(c_397,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_385])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_342,c_281,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.38  
% 2.39/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.38  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.39/1.38  
% 2.39/1.38  %Foreground sorts:
% 2.39/1.38  
% 2.39/1.38  
% 2.39/1.38  %Background operators:
% 2.39/1.38  
% 2.39/1.38  
% 2.39/1.38  %Foreground operators:
% 2.39/1.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.39/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.39/1.38  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.39/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.38  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.39/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.39/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.38  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.39/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.38  
% 2.67/1.40  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.67/1.40  tff(f_93, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.67/1.40  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.67/1.40  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.67/1.40  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.67/1.40  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.67/1.40  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.67/1.40  tff(f_86, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.67/1.40  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.67/1.40  tff(f_84, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.67/1.40  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.67/1.40  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.67/1.40  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.67/1.40  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.67/1.40  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.40  tff(c_51, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.40  tff(c_57, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_51])).
% 2.67/1.40  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_57])).
% 2.67/1.40  tff(c_327, plain, (![A_113, B_114, C_115, D_116]: (r2_relset_1(A_113, B_114, C_115, C_115) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.67/1.40  tff(c_339, plain, (![C_120]: (r2_relset_1('#skF_1', '#skF_2', C_120, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_36, c_327])).
% 2.67/1.40  tff(c_342, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_339])).
% 2.67/1.40  tff(c_224, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.40  tff(c_232, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_224])).
% 2.67/1.40  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.40  tff(c_264, plain, (![A_102, B_103]: (k8_relat_1(A_102, B_103)=B_103 | ~r1_tarski(k2_relat_1(B_103), A_102) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.67/1.40  tff(c_269, plain, (![A_104, B_105]: (k8_relat_1(A_104, B_105)=B_105 | ~v5_relat_1(B_105, A_104) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_10, c_264])).
% 2.67/1.40  tff(c_275, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_232, c_269])).
% 2.67/1.40  tff(c_281, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_275])).
% 2.67/1.40  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.67/1.40  tff(c_14, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=k8_relat_1(A_10, B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.67/1.40  tff(c_38, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_partfun1(A_10))=k8_relat_1(A_10, B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 2.67/1.40  tff(c_30, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.67/1.40  tff(c_343, plain, (![C_121, A_124, D_126, E_122, B_123, F_125]: (k4_relset_1(A_124, B_123, C_121, D_126, E_122, F_125)=k5_relat_1(E_122, F_125) | ~m1_subset_1(F_125, k1_zfmisc_1(k2_zfmisc_1(C_121, D_126))) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.40  tff(c_378, plain, (![A_131, B_132, A_133, E_134]: (k4_relset_1(A_131, B_132, A_133, A_133, E_134, k6_partfun1(A_133))=k5_relat_1(E_134, k6_partfun1(A_133)) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(resolution, [status(thm)], [c_30, c_343])).
% 2.67/1.40  tff(c_384, plain, (![A_133]: (k4_relset_1('#skF_1', '#skF_2', A_133, A_133, '#skF_3', k6_partfun1(A_133))=k5_relat_1('#skF_3', k6_partfun1(A_133)))), inference(resolution, [status(thm)], [c_36, c_378])).
% 2.67/1.40  tff(c_77, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.40  tff(c_85, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_77])).
% 2.67/1.40  tff(c_170, plain, (![A_68, B_69, C_70, D_71]: (r2_relset_1(A_68, B_69, C_70, C_70) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.67/1.40  tff(c_182, plain, (![C_75]: (r2_relset_1('#skF_1', '#skF_2', C_75, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_36, c_170])).
% 2.67/1.40  tff(c_185, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_182])).
% 2.67/1.40  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.40  tff(c_18, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.40  tff(c_138, plain, (![A_62, B_63]: (k5_relat_1(k6_partfun1(A_62), B_63)=B_63 | ~r1_tarski(k1_relat_1(B_63), A_62) | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_18])).
% 2.67/1.40  tff(c_142, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_138])).
% 2.67/1.40  tff(c_186, plain, (![D_81, B_78, F_80, E_77, C_76, A_79]: (k4_relset_1(A_79, B_78, C_76, D_81, E_77, F_80)=k5_relat_1(E_77, F_80) | ~m1_subset_1(F_80, k1_zfmisc_1(k2_zfmisc_1(C_76, D_81))) | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.40  tff(c_193, plain, (![A_82, B_83, E_84]: (k4_relset_1(A_82, B_83, '#skF_1', '#skF_2', E_84, '#skF_3')=k5_relat_1(E_84, '#skF_3') | ~m1_subset_1(E_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(resolution, [status(thm)], [c_36, c_186])).
% 2.67/1.40  tff(c_200, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_193])).
% 2.67/1.40  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.40  tff(c_66, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.67/1.40  tff(c_206, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_66])).
% 2.67/1.40  tff(c_218, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_206])).
% 2.67/1.40  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_85, c_185, c_218])).
% 2.67/1.40  tff(c_222, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.67/1.40  tff(c_385, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_222])).
% 2.67/1.40  tff(c_397, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_385])).
% 2.67/1.40  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_342, c_281, c_397])).
% 2.67/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  Inference rules
% 2.67/1.40  ----------------------
% 2.67/1.40  #Ref     : 0
% 2.67/1.40  #Sup     : 77
% 2.67/1.40  #Fact    : 0
% 2.67/1.40  #Define  : 0
% 2.67/1.40  #Split   : 1
% 2.67/1.40  #Chain   : 0
% 2.67/1.40  #Close   : 0
% 2.67/1.40  
% 2.67/1.40  Ordering : KBO
% 2.67/1.40  
% 2.67/1.40  Simplification rules
% 2.67/1.40  ----------------------
% 2.67/1.40  #Subsume      : 2
% 2.67/1.40  #Demod        : 30
% 2.67/1.40  #Tautology    : 35
% 2.67/1.40  #SimpNegUnit  : 0
% 2.67/1.40  #BackRed      : 3
% 2.67/1.40  
% 2.67/1.40  #Partial instantiations: 0
% 2.67/1.40  #Strategies tried      : 1
% 2.67/1.40  
% 2.67/1.40  Timing (in seconds)
% 2.67/1.40  ----------------------
% 2.67/1.40  Preprocessing        : 0.32
% 2.67/1.40  Parsing              : 0.18
% 2.67/1.40  CNF conversion       : 0.02
% 2.67/1.40  Main loop            : 0.27
% 2.67/1.40  Inferencing          : 0.12
% 2.67/1.40  Reduction            : 0.08
% 2.67/1.40  Demodulation         : 0.06
% 2.67/1.40  BG Simplification    : 0.02
% 2.67/1.40  Subsumption          : 0.03
% 2.67/1.40  Abstraction          : 0.02
% 2.67/1.40  MUC search           : 0.00
% 2.67/1.40  Cooper               : 0.00
% 2.67/1.40  Total                : 0.63
% 2.67/1.40  Index Insertion      : 0.00
% 2.67/1.40  Index Deletion       : 0.00
% 2.67/1.40  Index Matching       : 0.00
% 2.67/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
