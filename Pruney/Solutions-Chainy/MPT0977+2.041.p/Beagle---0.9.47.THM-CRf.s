%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:51 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 134 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :    7
%              Number of atoms          :  110 ( 213 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_82,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_47,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_59,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_53])).

tff(c_329,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( r2_relset_1(A_105,B_106,C_107,C_107)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_340,plain,(
    ! [C_109] :
      ( r2_relset_1('#skF_1','#skF_2',C_109,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_329])).

tff(c_343,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_340])).

tff(c_70,plain,(
    ! [C_40,B_41,A_42] :
      ( v5_relat_1(C_40,B_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_42,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_311,plain,(
    ! [A_101,B_102] :
      ( k8_relat_1(A_101,B_102) = B_102
      | ~ r1_tarski(k2_relat_1(B_102),A_101)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_316,plain,(
    ! [A_103,B_104] :
      ( k8_relat_1(A_103,B_104) = B_104
      | ~ v5_relat_1(B_104,A_103)
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_6,c_311])).

tff(c_322,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_316])).

tff(c_328,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_322])).

tff(c_28,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_35,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_partfun1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_26,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_33,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_344,plain,(
    ! [C_110,A_113,E_111,D_115,F_114,B_112] :
      ( k4_relset_1(A_113,B_112,C_110,D_115,E_111,F_114) = k5_relat_1(E_111,F_114)
      | ~ m1_subset_1(F_114,k1_zfmisc_1(k2_zfmisc_1(C_110,D_115)))
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_379,plain,(
    ! [A_123,B_124,A_125,E_126] :
      ( k4_relset_1(A_123,B_124,A_125,A_125,E_126,k6_partfun1(A_125)) = k5_relat_1(E_126,k6_partfun1(A_125))
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(resolution,[status(thm)],[c_33,c_344])).

tff(c_385,plain,(
    ! [A_125] : k4_relset_1('#skF_1','#skF_2',A_125,A_125,'#skF_3',k6_partfun1(A_125)) = k5_relat_1('#skF_3',k6_partfun1(A_125)) ),
    inference(resolution,[status(thm)],[c_32,c_379])).

tff(c_159,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( r2_relset_1(A_61,B_62,C_63,C_63)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_183,plain,(
    ! [C_67] :
      ( r2_relset_1('#skF_1','#skF_2',C_67,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_159])).

tff(c_186,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_183])).

tff(c_112,plain,(
    ! [C_48,A_49,B_50] :
      ( v4_relat_1(C_48,A_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_120,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_112])).

tff(c_123,plain,(
    ! [B_54,A_55] :
      ( k7_relat_1(B_54,A_55) = B_54
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_129,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_123])).

tff(c_135,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_129])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_partfun1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_192,plain,(
    ! [E_72,A_74,B_73,F_75,C_71,D_76] :
      ( k4_relset_1(A_74,B_73,C_71,D_76,E_72,F_75) = k5_relat_1(E_72,F_75)
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(C_71,D_76)))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_199,plain,(
    ! [A_77,B_78,E_79] :
      ( k4_relset_1(A_77,B_78,'#skF_1','#skF_2',E_79,'#skF_3') = k5_relat_1(E_79,'#skF_3')
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(resolution,[status(thm)],[c_32,c_192])).

tff(c_206,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_33,c_199])).

tff(c_30,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_79,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_219,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_79])).

tff(c_231,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_219])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_186,c_135,c_231])).

tff(c_235,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_391,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_235])).

tff(c_403,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_391])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_343,c_328,c_403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:42:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.36  
% 2.28/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.37  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.37  
% 2.28/1.37  %Foreground sorts:
% 2.28/1.37  
% 2.28/1.37  
% 2.28/1.37  %Background operators:
% 2.28/1.37  
% 2.28/1.37  
% 2.28/1.37  %Foreground operators:
% 2.28/1.37  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.28/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.28/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.28/1.37  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.37  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.28/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.37  
% 2.58/1.39  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.58/1.39  tff(f_89, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.58/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.58/1.39  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.58/1.39  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.58/1.39  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.58/1.39  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.58/1.39  tff(f_82, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.58/1.39  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.58/1.39  tff(f_80, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.58/1.39  tff(f_72, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.58/1.39  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.58/1.39  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.58/1.39  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.58/1.39  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.39  tff(c_47, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.58/1.39  tff(c_53, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.58/1.39  tff(c_59, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_53])).
% 2.58/1.39  tff(c_329, plain, (![A_105, B_106, C_107, D_108]: (r2_relset_1(A_105, B_106, C_107, C_107) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.58/1.39  tff(c_340, plain, (![C_109]: (r2_relset_1('#skF_1', '#skF_2', C_109, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_329])).
% 2.58/1.39  tff(c_343, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_340])).
% 2.58/1.39  tff(c_70, plain, (![C_40, B_41, A_42]: (v5_relat_1(C_40, B_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_42, B_41))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.58/1.39  tff(c_78, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_70])).
% 2.58/1.39  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.39  tff(c_311, plain, (![A_101, B_102]: (k8_relat_1(A_101, B_102)=B_102 | ~r1_tarski(k2_relat_1(B_102), A_101) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.39  tff(c_316, plain, (![A_103, B_104]: (k8_relat_1(A_103, B_104)=B_104 | ~v5_relat_1(B_104, A_103) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_6, c_311])).
% 2.58/1.39  tff(c_322, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_316])).
% 2.58/1.39  tff(c_328, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_322])).
% 2.58/1.39  tff(c_28, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.39  tff(c_10, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.58/1.39  tff(c_35, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_partfun1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10])).
% 2.58/1.39  tff(c_26, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.58/1.39  tff(c_33, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.58/1.39  tff(c_344, plain, (![C_110, A_113, E_111, D_115, F_114, B_112]: (k4_relset_1(A_113, B_112, C_110, D_115, E_111, F_114)=k5_relat_1(E_111, F_114) | ~m1_subset_1(F_114, k1_zfmisc_1(k2_zfmisc_1(C_110, D_115))) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.58/1.39  tff(c_379, plain, (![A_123, B_124, A_125, E_126]: (k4_relset_1(A_123, B_124, A_125, A_125, E_126, k6_partfun1(A_125))=k5_relat_1(E_126, k6_partfun1(A_125)) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(resolution, [status(thm)], [c_33, c_344])).
% 2.58/1.39  tff(c_385, plain, (![A_125]: (k4_relset_1('#skF_1', '#skF_2', A_125, A_125, '#skF_3', k6_partfun1(A_125))=k5_relat_1('#skF_3', k6_partfun1(A_125)))), inference(resolution, [status(thm)], [c_32, c_379])).
% 2.58/1.39  tff(c_159, plain, (![A_61, B_62, C_63, D_64]: (r2_relset_1(A_61, B_62, C_63, C_63) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.58/1.39  tff(c_183, plain, (![C_67]: (r2_relset_1('#skF_1', '#skF_2', C_67, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_32, c_159])).
% 2.58/1.39  tff(c_186, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_183])).
% 2.58/1.39  tff(c_112, plain, (![C_48, A_49, B_50]: (v4_relat_1(C_48, A_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.58/1.39  tff(c_120, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_112])).
% 2.58/1.39  tff(c_123, plain, (![B_54, A_55]: (k7_relat_1(B_54, A_55)=B_54 | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.58/1.39  tff(c_129, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_123])).
% 2.58/1.39  tff(c_135, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_129])).
% 2.58/1.39  tff(c_16, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.39  tff(c_34, plain, (![A_14, B_15]: (k5_relat_1(k6_partfun1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_16])).
% 2.58/1.39  tff(c_192, plain, (![E_72, A_74, B_73, F_75, C_71, D_76]: (k4_relset_1(A_74, B_73, C_71, D_76, E_72, F_75)=k5_relat_1(E_72, F_75) | ~m1_subset_1(F_75, k1_zfmisc_1(k2_zfmisc_1(C_71, D_76))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.58/1.39  tff(c_199, plain, (![A_77, B_78, E_79]: (k4_relset_1(A_77, B_78, '#skF_1', '#skF_2', E_79, '#skF_3')=k5_relat_1(E_79, '#skF_3') | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(resolution, [status(thm)], [c_32, c_192])).
% 2.58/1.39  tff(c_206, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_33, c_199])).
% 2.58/1.39  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.58/1.39  tff(c_79, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.58/1.39  tff(c_219, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_79])).
% 2.58/1.39  tff(c_231, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_219])).
% 2.58/1.39  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_186, c_135, c_231])).
% 2.58/1.39  tff(c_235, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.58/1.39  tff(c_391, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_235])).
% 2.58/1.39  tff(c_403, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_35, c_391])).
% 2.58/1.39  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_343, c_328, c_403])).
% 2.58/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  
% 2.58/1.39  Inference rules
% 2.58/1.39  ----------------------
% 2.58/1.39  #Ref     : 0
% 2.58/1.39  #Sup     : 81
% 2.58/1.39  #Fact    : 0
% 2.58/1.39  #Define  : 0
% 2.58/1.39  #Split   : 1
% 2.58/1.39  #Chain   : 0
% 2.58/1.39  #Close   : 0
% 2.58/1.39  
% 2.58/1.39  Ordering : KBO
% 2.58/1.39  
% 2.58/1.39  Simplification rules
% 2.58/1.39  ----------------------
% 2.58/1.39  #Subsume      : 0
% 2.58/1.39  #Demod        : 39
% 2.58/1.39  #Tautology    : 41
% 2.58/1.39  #SimpNegUnit  : 0
% 2.58/1.39  #BackRed      : 3
% 2.58/1.39  
% 2.58/1.39  #Partial instantiations: 0
% 2.58/1.39  #Strategies tried      : 1
% 2.58/1.39  
% 2.58/1.39  Timing (in seconds)
% 2.58/1.39  ----------------------
% 2.58/1.39  Preprocessing        : 0.33
% 2.58/1.39  Parsing              : 0.18
% 2.58/1.39  CNF conversion       : 0.02
% 2.58/1.39  Main loop            : 0.24
% 2.58/1.39  Inferencing          : 0.10
% 2.58/1.39  Reduction            : 0.08
% 2.58/1.39  Demodulation         : 0.05
% 2.58/1.39  BG Simplification    : 0.01
% 2.58/1.39  Subsumption          : 0.03
% 2.58/1.39  Abstraction          : 0.02
% 2.58/1.39  MUC search           : 0.00
% 2.58/1.39  Cooper               : 0.00
% 2.58/1.39  Total                : 0.61
% 2.58/1.39  Index Insertion      : 0.00
% 2.58/1.39  Index Deletion       : 0.00
% 2.58/1.39  Index Matching       : 0.00
% 2.58/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
