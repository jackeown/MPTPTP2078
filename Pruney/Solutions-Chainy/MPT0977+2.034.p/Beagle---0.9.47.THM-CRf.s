%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:50 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 129 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :    6
%              Number of atoms          :  110 ( 209 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_66,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_84,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_49,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_353,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_relset_1(A_109,B_110,C_111,C_111)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_365,plain,(
    ! [C_116] :
      ( r2_relset_1('#skF_1','#skF_2',C_116,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_353])).

tff(c_368,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_365])).

tff(c_63,plain,(
    ! [C_39,B_40,A_41] :
      ( v5_relat_1(C_39,B_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_41,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_331,plain,(
    ! [A_105,B_106] :
      ( k8_relat_1(A_105,B_106) = B_106
      | ~ r1_tarski(k2_relat_1(B_106),A_105)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_336,plain,(
    ! [A_107,B_108] :
      ( k8_relat_1(A_107,B_108) = B_108
      | ~ v5_relat_1(B_108,A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_6,c_331])).

tff(c_342,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_336])).

tff(c_348,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_342])).

tff(c_30,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_partfun1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_28,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_369,plain,(
    ! [D_122,B_119,A_120,F_121,C_117,E_118] :
      ( k4_relset_1(A_120,B_119,C_117,D_122,E_118,F_121) = k5_relat_1(E_118,F_121)
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_117,D_122)))
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_404,plain,(
    ! [A_127,B_128,A_129,E_130] :
      ( k4_relset_1(A_127,B_128,A_129,A_129,E_130,k6_partfun1(A_129)) = k5_relat_1(E_130,k6_partfun1(A_129))
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(resolution,[status(thm)],[c_28,c_369])).

tff(c_410,plain,(
    ! [A_129] : k4_relset_1('#skF_1','#skF_2',A_129,A_129,'#skF_3',k6_partfun1(A_129)) = k5_relat_1('#skF_3',k6_partfun1(A_129)) ),
    inference(resolution,[status(thm)],[c_34,c_404])).

tff(c_178,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( r2_relset_1(A_64,B_65,C_66,C_66)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_185,plain,(
    ! [C_68] :
      ( r2_relset_1('#skF_1','#skF_2',C_68,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_178])).

tff(c_188,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_185])).

tff(c_84,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_84])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_96,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_14])).

tff(c_99,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_96])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_partfun1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16])).

tff(c_194,plain,(
    ! [D_77,E_73,B_74,F_76,C_72,A_75] :
      ( k4_relset_1(A_75,B_74,C_72,D_77,E_73,F_76) = k5_relat_1(E_73,F_76)
      | ~ m1_subset_1(F_76,k1_zfmisc_1(k2_zfmisc_1(C_72,D_77)))
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_201,plain,(
    ! [A_78,B_79,E_80] :
      ( k4_relset_1(A_78,B_79,'#skF_1','#skF_2',E_80,'#skF_3') = k5_relat_1(E_80,'#skF_3')
      | ~ m1_subset_1(E_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(resolution,[status(thm)],[c_34,c_194])).

tff(c_208,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_201])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_72,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_230,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_72])).

tff(c_242,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_230])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_188,c_99,c_242])).

tff(c_246,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_411,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_246])).

tff(c_423,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_411])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_368,c_348,c_423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:43:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  
% 2.29/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.32  
% 2.29/1.32  %Foreground sorts:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Background operators:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Foreground operators:
% 2.29/1.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.29/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.29/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.29/1.32  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.29/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.29/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.29/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.32  
% 2.59/1.34  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.59/1.34  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.59/1.34  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.59/1.34  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.59/1.34  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.59/1.34  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.59/1.34  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.59/1.34  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.59/1.34  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.59/1.34  tff(f_82, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.59/1.34  tff(f_72, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.59/1.34  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.59/1.34  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.59/1.34  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.59/1.34  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.59/1.34  tff(c_49, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.34  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.59/1.34  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_55])).
% 2.59/1.34  tff(c_353, plain, (![A_109, B_110, C_111, D_112]: (r2_relset_1(A_109, B_110, C_111, C_111) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.34  tff(c_365, plain, (![C_116]: (r2_relset_1('#skF_1', '#skF_2', C_116, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_353])).
% 2.59/1.34  tff(c_368, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_365])).
% 2.59/1.34  tff(c_63, plain, (![C_39, B_40, A_41]: (v5_relat_1(C_39, B_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_41, B_40))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.59/1.34  tff(c_71, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_63])).
% 2.59/1.34  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.34  tff(c_331, plain, (![A_105, B_106]: (k8_relat_1(A_105, B_106)=B_106 | ~r1_tarski(k2_relat_1(B_106), A_105) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.34  tff(c_336, plain, (![A_107, B_108]: (k8_relat_1(A_107, B_108)=B_108 | ~v5_relat_1(B_108, A_107) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_6, c_331])).
% 2.59/1.34  tff(c_342, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_336])).
% 2.59/1.34  tff(c_348, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_342])).
% 2.59/1.34  tff(c_30, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.59/1.34  tff(c_10, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.34  tff(c_36, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_partfun1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 2.59/1.34  tff(c_28, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.59/1.34  tff(c_369, plain, (![D_122, B_119, A_120, F_121, C_117, E_118]: (k4_relset_1(A_120, B_119, C_117, D_122, E_118, F_121)=k5_relat_1(E_118, F_121) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_117, D_122))) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.59/1.34  tff(c_404, plain, (![A_127, B_128, A_129, E_130]: (k4_relset_1(A_127, B_128, A_129, A_129, E_130, k6_partfun1(A_129))=k5_relat_1(E_130, k6_partfun1(A_129)) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(resolution, [status(thm)], [c_28, c_369])).
% 2.59/1.34  tff(c_410, plain, (![A_129]: (k4_relset_1('#skF_1', '#skF_2', A_129, A_129, '#skF_3', k6_partfun1(A_129))=k5_relat_1('#skF_3', k6_partfun1(A_129)))), inference(resolution, [status(thm)], [c_34, c_404])).
% 2.59/1.34  tff(c_178, plain, (![A_64, B_65, C_66, D_67]: (r2_relset_1(A_64, B_65, C_66, C_66) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.59/1.34  tff(c_185, plain, (![C_68]: (r2_relset_1('#skF_1', '#skF_2', C_68, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_178])).
% 2.59/1.34  tff(c_188, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_185])).
% 2.59/1.34  tff(c_84, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.59/1.34  tff(c_92, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_84])).
% 2.59/1.34  tff(c_14, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.59/1.34  tff(c_96, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_14])).
% 2.59/1.34  tff(c_99, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_96])).
% 2.59/1.34  tff(c_16, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.59/1.34  tff(c_35, plain, (![A_14, B_15]: (k5_relat_1(k6_partfun1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16])).
% 2.59/1.34  tff(c_194, plain, (![D_77, E_73, B_74, F_76, C_72, A_75]: (k4_relset_1(A_75, B_74, C_72, D_77, E_73, F_76)=k5_relat_1(E_73, F_76) | ~m1_subset_1(F_76, k1_zfmisc_1(k2_zfmisc_1(C_72, D_77))) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.59/1.34  tff(c_201, plain, (![A_78, B_79, E_80]: (k4_relset_1(A_78, B_79, '#skF_1', '#skF_2', E_80, '#skF_3')=k5_relat_1(E_80, '#skF_3') | ~m1_subset_1(E_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(resolution, [status(thm)], [c_34, c_194])).
% 2.59/1.34  tff(c_208, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_201])).
% 2.59/1.34  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.59/1.34  tff(c_72, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.59/1.34  tff(c_230, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_72])).
% 2.59/1.34  tff(c_242, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_35, c_230])).
% 2.59/1.34  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_188, c_99, c_242])).
% 2.59/1.34  tff(c_246, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.59/1.34  tff(c_411, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_246])).
% 2.59/1.34  tff(c_423, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_411])).
% 2.59/1.34  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_368, c_348, c_423])).
% 2.59/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.34  
% 2.59/1.34  Inference rules
% 2.59/1.34  ----------------------
% 2.59/1.34  #Ref     : 0
% 2.59/1.34  #Sup     : 85
% 2.59/1.34  #Fact    : 0
% 2.59/1.34  #Define  : 0
% 2.59/1.34  #Split   : 1
% 2.59/1.34  #Chain   : 0
% 2.59/1.34  #Close   : 0
% 2.59/1.34  
% 2.59/1.34  Ordering : KBO
% 2.59/1.34  
% 2.59/1.34  Simplification rules
% 2.59/1.34  ----------------------
% 2.59/1.34  #Subsume      : 0
% 2.59/1.34  #Demod        : 38
% 2.59/1.34  #Tautology    : 45
% 2.59/1.34  #SimpNegUnit  : 0
% 2.59/1.34  #BackRed      : 3
% 2.59/1.34  
% 2.59/1.34  #Partial instantiations: 0
% 2.59/1.34  #Strategies tried      : 1
% 2.59/1.34  
% 2.59/1.34  Timing (in seconds)
% 2.59/1.34  ----------------------
% 2.59/1.34  Preprocessing        : 0.31
% 2.59/1.34  Parsing              : 0.17
% 2.59/1.34  CNF conversion       : 0.02
% 2.59/1.34  Main loop            : 0.27
% 2.59/1.34  Inferencing          : 0.11
% 2.59/1.34  Reduction            : 0.08
% 2.59/1.34  Demodulation         : 0.06
% 2.59/1.34  BG Simplification    : 0.02
% 2.59/1.34  Subsumption          : 0.03
% 2.59/1.34  Abstraction          : 0.02
% 2.59/1.34  MUC search           : 0.00
% 2.59/1.34  Cooper               : 0.00
% 2.59/1.35  Total                : 0.62
% 2.59/1.35  Index Insertion      : 0.00
% 2.59/1.35  Index Deletion       : 0.00
% 2.59/1.35  Index Matching       : 0.00
% 2.59/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
