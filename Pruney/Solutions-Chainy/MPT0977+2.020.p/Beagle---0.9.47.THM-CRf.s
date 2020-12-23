%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:48 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 101 expanded)
%              Number of leaves         :   33 (  49 expanded)
%              Depth                    :    6
%              Number of atoms          :  104 ( 166 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_91,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_84,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_70,axiom,(
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

tff(f_52,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_51,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_57])).

tff(c_205,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_213,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_205])).

tff(c_241,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_relset_1(A_97,B_98,D_99,D_99)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_247,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_241])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_236,plain,(
    ! [B_95,A_96] :
      ( k5_relat_1(B_95,k6_partfun1(A_96)) = B_95
      | ~ r1_tarski(k2_relat_1(B_95),A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_240,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_partfun1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_236])).

tff(c_30,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_310,plain,(
    ! [B_115,F_116,D_117,E_118,A_114,C_113] :
      ( k4_relset_1(A_114,B_115,C_113,D_117,E_118,F_116) = k5_relat_1(E_118,F_116)
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_113,D_117)))
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_378,plain,(
    ! [A_123,B_124,A_125,E_126] :
      ( k4_relset_1(A_123,B_124,A_125,A_125,E_126,k6_partfun1(A_125)) = k5_relat_1(E_126,k6_partfun1(A_125))
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(resolution,[status(thm)],[c_30,c_310])).

tff(c_384,plain,(
    ! [A_125] : k4_relset_1('#skF_1','#skF_2',A_125,A_125,'#skF_3',k6_partfun1(A_125)) = k5_relat_1('#skF_3',k6_partfun1(A_125)) ),
    inference(resolution,[status(thm)],[c_36,c_378])).

tff(c_77,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_98,plain,(
    ! [A_53,B_54,D_55] :
      ( r2_relset_1(A_53,B_54,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = B_11
      | ~ r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_partfun1(A_57),B_58) = B_58
      | ~ r1_tarski(k1_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_110,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_167,plain,(
    ! [F_74,B_73,E_76,A_72,D_75,C_71] :
      ( k4_relset_1(A_72,B_73,C_71,D_75,E_76,F_74) = k5_relat_1(E_76,F_74)
      | ~ m1_subset_1(F_74,k1_zfmisc_1(k2_zfmisc_1(C_71,D_75)))
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_174,plain,(
    ! [A_77,B_78,E_79] :
      ( k4_relset_1(A_77,B_78,'#skF_1','#skF_2',E_79,'#skF_3') = k5_relat_1(E_79,'#skF_3')
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(resolution,[status(thm)],[c_36,c_167])).

tff(c_181,plain,(
    ! [A_27] : k4_relset_1(A_27,A_27,'#skF_1','#skF_2',k6_partfun1(A_27),'#skF_3') = k5_relat_1(k6_partfun1(A_27),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_174])).

tff(c_34,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_187,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_66])).

tff(c_199,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_187])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_85,c_104,c_199])).

tff(c_203,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_385,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_203])).

tff(c_397,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_385])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_213,c_247,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.43  
% 2.42/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.43  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.42/1.43  
% 2.42/1.43  %Foreground sorts:
% 2.42/1.43  
% 2.42/1.43  
% 2.42/1.43  %Background operators:
% 2.42/1.43  
% 2.42/1.43  
% 2.42/1.43  %Foreground operators:
% 2.42/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.42/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.42/1.43  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.42/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.42/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.42/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.42/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.42/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.43  
% 2.42/1.45  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.42/1.45  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.42/1.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.42/1.45  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.42/1.45  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.42/1.45  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.42/1.45  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.42/1.45  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.42/1.45  tff(f_82, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.42/1.45  tff(f_70, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.42/1.45  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.42/1.45  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.42/1.45  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.42/1.45  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.42/1.45  tff(c_51, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.42/1.45  tff(c_57, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_51])).
% 2.42/1.45  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_57])).
% 2.42/1.45  tff(c_205, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.45  tff(c_213, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_205])).
% 2.42/1.45  tff(c_241, plain, (![A_97, B_98, D_99]: (r2_relset_1(A_97, B_98, D_99, D_99) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.42/1.45  tff(c_247, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_241])).
% 2.42/1.45  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.42/1.45  tff(c_32, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.42/1.45  tff(c_16, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.42/1.45  tff(c_236, plain, (![B_95, A_96]: (k5_relat_1(B_95, k6_partfun1(A_96))=B_95 | ~r1_tarski(k2_relat_1(B_95), A_96) | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 2.42/1.45  tff(c_240, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_partfun1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_236])).
% 2.42/1.45  tff(c_30, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.42/1.45  tff(c_310, plain, (![B_115, F_116, D_117, E_118, A_114, C_113]: (k4_relset_1(A_114, B_115, C_113, D_117, E_118, F_116)=k5_relat_1(E_118, F_116) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_113, D_117))) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.42/1.45  tff(c_378, plain, (![A_123, B_124, A_125, E_126]: (k4_relset_1(A_123, B_124, A_125, A_125, E_126, k6_partfun1(A_125))=k5_relat_1(E_126, k6_partfun1(A_125)) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(resolution, [status(thm)], [c_30, c_310])).
% 2.42/1.45  tff(c_384, plain, (![A_125]: (k4_relset_1('#skF_1', '#skF_2', A_125, A_125, '#skF_3', k6_partfun1(A_125))=k5_relat_1('#skF_3', k6_partfun1(A_125)))), inference(resolution, [status(thm)], [c_36, c_378])).
% 2.42/1.45  tff(c_77, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.45  tff(c_85, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_77])).
% 2.42/1.45  tff(c_98, plain, (![A_53, B_54, D_55]: (r2_relset_1(A_53, B_54, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.42/1.45  tff(c_104, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_98])).
% 2.42/1.45  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.42/1.45  tff(c_14, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=B_11 | ~r1_tarski(k1_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.42/1.45  tff(c_106, plain, (![A_57, B_58]: (k5_relat_1(k6_partfun1(A_57), B_58)=B_58 | ~r1_tarski(k1_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 2.42/1.45  tff(c_110, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_106])).
% 2.42/1.45  tff(c_167, plain, (![F_74, B_73, E_76, A_72, D_75, C_71]: (k4_relset_1(A_72, B_73, C_71, D_75, E_76, F_74)=k5_relat_1(E_76, F_74) | ~m1_subset_1(F_74, k1_zfmisc_1(k2_zfmisc_1(C_71, D_75))) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.42/1.45  tff(c_174, plain, (![A_77, B_78, E_79]: (k4_relset_1(A_77, B_78, '#skF_1', '#skF_2', E_79, '#skF_3')=k5_relat_1(E_79, '#skF_3') | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(resolution, [status(thm)], [c_36, c_167])).
% 2.42/1.45  tff(c_181, plain, (![A_27]: (k4_relset_1(A_27, A_27, '#skF_1', '#skF_2', k6_partfun1(A_27), '#skF_3')=k5_relat_1(k6_partfun1(A_27), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_174])).
% 2.42/1.45  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.42/1.45  tff(c_66, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.42/1.45  tff(c_187, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_66])).
% 2.42/1.45  tff(c_199, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_110, c_187])).
% 2.42/1.45  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_85, c_104, c_199])).
% 2.42/1.45  tff(c_203, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.42/1.45  tff(c_385, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_203])).
% 2.42/1.45  tff(c_397, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_240, c_385])).
% 2.42/1.45  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_213, c_247, c_397])).
% 2.42/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.45  
% 2.42/1.45  Inference rules
% 2.42/1.45  ----------------------
% 2.42/1.45  #Ref     : 0
% 2.42/1.45  #Sup     : 72
% 2.42/1.45  #Fact    : 0
% 2.42/1.45  #Define  : 0
% 2.42/1.45  #Split   : 2
% 2.42/1.45  #Chain   : 0
% 2.42/1.45  #Close   : 0
% 2.42/1.45  
% 2.42/1.45  Ordering : KBO
% 2.42/1.45  
% 2.42/1.45  Simplification rules
% 2.42/1.45  ----------------------
% 2.42/1.45  #Subsume      : 2
% 2.42/1.45  #Demod        : 43
% 2.42/1.45  #Tautology    : 37
% 2.42/1.45  #SimpNegUnit  : 0
% 2.42/1.45  #BackRed      : 4
% 2.42/1.45  
% 2.42/1.45  #Partial instantiations: 0
% 2.42/1.45  #Strategies tried      : 1
% 2.42/1.45  
% 2.42/1.45  Timing (in seconds)
% 2.42/1.45  ----------------------
% 2.42/1.45  Preprocessing        : 0.33
% 2.42/1.45  Parsing              : 0.18
% 2.42/1.45  CNF conversion       : 0.02
% 2.42/1.45  Main loop            : 0.24
% 2.42/1.45  Inferencing          : 0.09
% 2.42/1.45  Reduction            : 0.08
% 2.42/1.45  Demodulation         : 0.06
% 2.42/1.45  BG Simplification    : 0.01
% 2.42/1.45  Subsumption          : 0.03
% 2.42/1.45  Abstraction          : 0.02
% 2.42/1.45  MUC search           : 0.00
% 2.42/1.45  Cooper               : 0.00
% 2.42/1.45  Total                : 0.60
% 2.42/1.45  Index Insertion      : 0.00
% 2.42/1.45  Index Deletion       : 0.00
% 2.42/1.45  Index Matching       : 0.00
% 2.42/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
