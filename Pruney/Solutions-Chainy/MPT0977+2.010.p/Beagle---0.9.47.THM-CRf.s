%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:46 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 128 expanded)
%              Number of leaves         :   36 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 205 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_85,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_428,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( r2_relset_1(A_111,B_112,C_113,C_113)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_440,plain,(
    ! [C_118] :
      ( r2_relset_1('#skF_1','#skF_2',C_118,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_428])).

tff(c_443,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_440])).

tff(c_318,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_326,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_318])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_337,plain,(
    ! [A_101,B_102] :
      ( k8_relat_1(A_101,B_102) = B_102
      | ~ r1_tarski(k2_relat_1(B_102),A_101)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_342,plain,(
    ! [A_103,B_104] :
      ( k8_relat_1(A_103,B_104) = B_104
      | ~ v5_relat_1(B_104,A_103)
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_4,c_337])).

tff(c_348,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_326,c_342])).

tff(c_354,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_348])).

tff(c_30,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_partfun1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6])).

tff(c_28,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_444,plain,(
    ! [A_122,B_121,F_123,C_119,D_124,E_120] :
      ( k4_relset_1(A_122,B_121,C_119,D_124,E_120,F_123) = k5_relat_1(E_120,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_119,D_124)))
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_475,plain,(
    ! [A_129,B_130,A_131,E_132] :
      ( k4_relset_1(A_129,B_130,A_131,A_131,E_132,k6_partfun1(A_131)) = k5_relat_1(E_132,k6_partfun1(A_131))
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(resolution,[status(thm)],[c_28,c_444])).

tff(c_481,plain,(
    ! [A_131] : k4_relset_1('#skF_1','#skF_2',A_131,A_131,'#skF_3',k6_partfun1(A_131)) = k5_relat_1('#skF_3',k6_partfun1(A_131)) ),
    inference(resolution,[status(thm)],[c_34,c_475])).

tff(c_187,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( r2_relset_1(A_64,B_65,C_66,C_66)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_224,plain,(
    ! [C_79] :
      ( r2_relset_1('#skF_1','#skF_2',C_79,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_187])).

tff(c_227,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_224])).

tff(c_61,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_86,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_86])).

tff(c_98,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_92])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_14])).

tff(c_106,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_102])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = B_10
      | ~ r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [A_60,B_61] :
      ( k5_relat_1(k6_partfun1(A_60),B_61) = B_61
      | ~ r1_tarski(k1_relat_1(B_61),A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_143,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_137])).

tff(c_152,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_143])).

tff(c_217,plain,(
    ! [A_76,B_75,C_73,D_78,E_74,F_77] :
      ( k4_relset_1(A_76,B_75,C_73,D_78,E_74,F_77) = k5_relat_1(E_74,F_77)
      | ~ m1_subset_1(F_77,k1_zfmisc_1(k2_zfmisc_1(C_73,D_78)))
      | ~ m1_subset_1(E_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_247,plain,(
    ! [A_82,B_83,E_84] :
      ( k4_relset_1(A_82,B_83,'#skF_1','#skF_2',E_84,'#skF_3') = k5_relat_1(E_84,'#skF_3')
      | ~ m1_subset_1(E_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(resolution,[status(thm)],[c_34,c_217])).

tff(c_254,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_247])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_260,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_60])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_152,c_260])).

tff(c_264,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_482,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_264])).

tff(c_494,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_482])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_443,c_354,c_494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:31:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.45  
% 2.45/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.45  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.45  
% 2.45/1.45  %Foreground sorts:
% 2.45/1.45  
% 2.45/1.45  
% 2.45/1.45  %Background operators:
% 2.45/1.45  
% 2.45/1.45  
% 2.45/1.45  %Foreground operators:
% 2.45/1.45  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.45/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.45  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.45/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.45/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.45/1.45  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.45/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.45  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.45/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.45/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.45/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.45/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.45/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.45  
% 2.84/1.47  tff(f_92, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.84/1.47  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.84/1.47  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.84/1.47  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.84/1.47  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.84/1.47  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.84/1.47  tff(f_85, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.84/1.47  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.84/1.47  tff(f_83, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.84/1.47  tff(f_73, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.84/1.47  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.84/1.47  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.84/1.47  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.84/1.47  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.47  tff(c_48, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.47  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_48])).
% 2.84/1.47  tff(c_428, plain, (![A_111, B_112, C_113, D_114]: (r2_relset_1(A_111, B_112, C_113, C_113) | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.84/1.47  tff(c_440, plain, (![C_118]: (r2_relset_1('#skF_1', '#skF_2', C_118, C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_428])).
% 2.84/1.47  tff(c_443, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_440])).
% 2.84/1.47  tff(c_318, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.84/1.47  tff(c_326, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_318])).
% 2.84/1.47  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.47  tff(c_337, plain, (![A_101, B_102]: (k8_relat_1(A_101, B_102)=B_102 | ~r1_tarski(k2_relat_1(B_102), A_101) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.47  tff(c_342, plain, (![A_103, B_104]: (k8_relat_1(A_103, B_104)=B_104 | ~v5_relat_1(B_104, A_103) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_4, c_337])).
% 2.84/1.47  tff(c_348, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_326, c_342])).
% 2.84/1.47  tff(c_354, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_348])).
% 2.84/1.47  tff(c_30, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.47  tff(c_6, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.47  tff(c_36, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_partfun1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6])).
% 2.84/1.47  tff(c_28, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.84/1.47  tff(c_444, plain, (![A_122, B_121, F_123, C_119, D_124, E_120]: (k4_relset_1(A_122, B_121, C_119, D_124, E_120, F_123)=k5_relat_1(E_120, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_119, D_124))) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.47  tff(c_475, plain, (![A_129, B_130, A_131, E_132]: (k4_relset_1(A_129, B_130, A_131, A_131, E_132, k6_partfun1(A_131))=k5_relat_1(E_132, k6_partfun1(A_131)) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(resolution, [status(thm)], [c_28, c_444])).
% 2.84/1.47  tff(c_481, plain, (![A_131]: (k4_relset_1('#skF_1', '#skF_2', A_131, A_131, '#skF_3', k6_partfun1(A_131))=k5_relat_1('#skF_3', k6_partfun1(A_131)))), inference(resolution, [status(thm)], [c_34, c_475])).
% 2.84/1.47  tff(c_187, plain, (![A_64, B_65, C_66, D_67]: (r2_relset_1(A_64, B_65, C_66, C_66) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.84/1.47  tff(c_224, plain, (![C_79]: (r2_relset_1('#skF_1', '#skF_2', C_79, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_187])).
% 2.84/1.47  tff(c_227, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_224])).
% 2.84/1.47  tff(c_61, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.84/1.47  tff(c_69, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_61])).
% 2.84/1.47  tff(c_86, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.84/1.47  tff(c_92, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_69, c_86])).
% 2.84/1.47  tff(c_98, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_92])).
% 2.84/1.47  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.47  tff(c_102, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_98, c_14])).
% 2.84/1.47  tff(c_106, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_102])).
% 2.84/1.47  tff(c_12, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=B_10 | ~r1_tarski(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.84/1.47  tff(c_137, plain, (![A_60, B_61]: (k5_relat_1(k6_partfun1(A_60), B_61)=B_61 | ~r1_tarski(k1_relat_1(B_61), A_60) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.84/1.47  tff(c_143, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_137])).
% 2.84/1.47  tff(c_152, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_143])).
% 2.84/1.47  tff(c_217, plain, (![A_76, B_75, C_73, D_78, E_74, F_77]: (k4_relset_1(A_76, B_75, C_73, D_78, E_74, F_77)=k5_relat_1(E_74, F_77) | ~m1_subset_1(F_77, k1_zfmisc_1(k2_zfmisc_1(C_73, D_78))) | ~m1_subset_1(E_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.47  tff(c_247, plain, (![A_82, B_83, E_84]: (k4_relset_1(A_82, B_83, '#skF_1', '#skF_2', E_84, '#skF_3')=k5_relat_1(E_84, '#skF_3') | ~m1_subset_1(E_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(resolution, [status(thm)], [c_34, c_217])).
% 2.84/1.47  tff(c_254, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_247])).
% 2.84/1.47  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.47  tff(c_60, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.84/1.47  tff(c_260, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_60])).
% 2.84/1.47  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_152, c_260])).
% 2.84/1.47  tff(c_264, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.84/1.47  tff(c_482, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_481, c_264])).
% 2.84/1.47  tff(c_494, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_482])).
% 2.84/1.47  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_443, c_354, c_494])).
% 2.84/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.47  
% 2.84/1.47  Inference rules
% 2.84/1.47  ----------------------
% 2.84/1.47  #Ref     : 0
% 2.84/1.47  #Sup     : 101
% 2.84/1.47  #Fact    : 0
% 2.84/1.47  #Define  : 0
% 2.84/1.47  #Split   : 1
% 2.84/1.47  #Chain   : 0
% 2.84/1.47  #Close   : 0
% 2.84/1.47  
% 2.84/1.47  Ordering : KBO
% 2.84/1.47  
% 2.84/1.47  Simplification rules
% 2.84/1.47  ----------------------
% 2.84/1.47  #Subsume      : 0
% 2.84/1.47  #Demod        : 56
% 2.84/1.47  #Tautology    : 53
% 2.84/1.47  #SimpNegUnit  : 0
% 2.84/1.47  #BackRed      : 3
% 2.84/1.47  
% 2.84/1.47  #Partial instantiations: 0
% 2.84/1.47  #Strategies tried      : 1
% 2.84/1.47  
% 2.84/1.47  Timing (in seconds)
% 2.84/1.47  ----------------------
% 2.84/1.47  Preprocessing        : 0.32
% 2.84/1.47  Parsing              : 0.16
% 2.84/1.47  CNF conversion       : 0.02
% 2.84/1.47  Main loop            : 0.34
% 2.84/1.47  Inferencing          : 0.14
% 2.84/1.47  Reduction            : 0.11
% 2.84/1.47  Demodulation         : 0.08
% 2.84/1.47  BG Simplification    : 0.02
% 2.84/1.47  Subsumption          : 0.04
% 2.84/1.47  Abstraction          : 0.02
% 2.84/1.47  MUC search           : 0.00
% 2.84/1.47  Cooper               : 0.00
% 2.84/1.47  Total                : 0.71
% 2.84/1.47  Index Insertion      : 0.00
% 2.84/1.47  Index Deletion       : 0.00
% 2.84/1.47  Index Matching       : 0.00
% 2.84/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
