%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:50 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 128 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 201 expanded)
%              Number of equality atoms :   25 (  33 expanded)
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

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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

tff(f_84,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_82,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_49,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_349,plain,(
    ! [A_107,B_108,D_109] :
      ( r2_relset_1(A_107,B_108,D_109,D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_355,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_349])).

tff(c_281,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_289,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_281])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_327,plain,(
    ! [A_103,B_104] :
      ( k8_relat_1(A_103,B_104) = B_104
      | ~ r1_tarski(k2_relat_1(B_104),A_103)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_332,plain,(
    ! [A_105,B_106] :
      ( k8_relat_1(A_105,B_106) = B_106
      | ~ v5_relat_1(B_106,A_105)
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_6,c_327])).

tff(c_338,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_332])).

tff(c_344,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_338])).

tff(c_30,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_partfun1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_28,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_35,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_439,plain,(
    ! [A_132,E_130,B_131,D_134,F_133,C_129] :
      ( k4_relset_1(A_132,B_131,C_129,D_134,E_130,F_133) = k5_relat_1(E_130,F_133)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(C_129,D_134)))
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_488,plain,(
    ! [A_139,B_140,A_141,E_142] :
      ( k4_relset_1(A_139,B_140,A_141,A_141,E_142,k6_partfun1(A_141)) = k5_relat_1(E_142,k6_partfun1(A_141))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(resolution,[status(thm)],[c_35,c_439])).

tff(c_494,plain,(
    ! [A_141] : k4_relset_1('#skF_1','#skF_2',A_141,A_141,'#skF_3',k6_partfun1(A_141)) = k5_relat_1('#skF_3',k6_partfun1(A_141)) ),
    inference(resolution,[status(thm)],[c_34,c_488])).

tff(c_161,plain,(
    ! [A_61,B_62,D_63] :
      ( r2_relset_1(A_61,B_62,D_63,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_167,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_161])).

tff(c_62,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_125,plain,(
    ! [B_54,A_55] :
      ( k7_relat_1(B_54,A_55) = B_54
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_125])).

tff(c_137,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_131])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_partfun1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16])).

tff(c_199,plain,(
    ! [E_72,A_74,B_73,F_75,C_71,D_76] :
      ( k4_relset_1(A_74,B_73,C_71,D_76,E_72,F_75) = k5_relat_1(E_72,F_75)
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(C_71,D_76)))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_206,plain,(
    ! [A_77,B_78,E_79] :
      ( k4_relset_1(A_77,B_78,'#skF_1','#skF_2',E_79,'#skF_3') = k5_relat_1(E_79,'#skF_3')
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(resolution,[status(thm)],[c_34,c_199])).

tff(c_213,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_206])).

tff(c_32,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_72,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_219,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_72])).

tff(c_238,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_219])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_167,c_137,c_238])).

tff(c_242,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_496,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_242])).

tff(c_508,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_496])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_355,c_344,c_508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:56:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.30  
% 2.22/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.22/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.22/1.31  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.22/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.22/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.31  
% 2.22/1.32  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.22/1.32  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_2)).
% 2.22/1.32  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.22/1.32  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.22/1.32  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.22/1.32  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.22/1.32  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.22/1.32  tff(f_84, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.22/1.32  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.22/1.32  tff(f_82, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.22/1.32  tff(f_72, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.22/1.32  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.22/1.32  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.22/1.32  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.22/1.32  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.22/1.32  tff(c_49, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.32  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.22/1.32  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_55])).
% 2.22/1.32  tff(c_349, plain, (![A_107, B_108, D_109]: (r2_relset_1(A_107, B_108, D_109, D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.32  tff(c_355, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_349])).
% 2.22/1.32  tff(c_281, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.22/1.32  tff(c_289, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_281])).
% 2.22/1.32  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.32  tff(c_327, plain, (![A_103, B_104]: (k8_relat_1(A_103, B_104)=B_104 | ~r1_tarski(k2_relat_1(B_104), A_103) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.22/1.32  tff(c_332, plain, (![A_105, B_106]: (k8_relat_1(A_105, B_106)=B_106 | ~v5_relat_1(B_106, A_105) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_6, c_327])).
% 2.22/1.32  tff(c_338, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_332])).
% 2.22/1.32  tff(c_344, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_338])).
% 2.22/1.32  tff(c_30, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.22/1.32  tff(c_10, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.32  tff(c_37, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_partfun1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 2.22/1.32  tff(c_28, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.22/1.32  tff(c_35, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 2.22/1.32  tff(c_439, plain, (![A_132, E_130, B_131, D_134, F_133, C_129]: (k4_relset_1(A_132, B_131, C_129, D_134, E_130, F_133)=k5_relat_1(E_130, F_133) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(C_129, D_134))) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.22/1.32  tff(c_488, plain, (![A_139, B_140, A_141, E_142]: (k4_relset_1(A_139, B_140, A_141, A_141, E_142, k6_partfun1(A_141))=k5_relat_1(E_142, k6_partfun1(A_141)) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(resolution, [status(thm)], [c_35, c_439])).
% 2.22/1.32  tff(c_494, plain, (![A_141]: (k4_relset_1('#skF_1', '#skF_2', A_141, A_141, '#skF_3', k6_partfun1(A_141))=k5_relat_1('#skF_3', k6_partfun1(A_141)))), inference(resolution, [status(thm)], [c_34, c_488])).
% 2.22/1.32  tff(c_161, plain, (![A_61, B_62, D_63]: (r2_relset_1(A_61, B_62, D_63, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.32  tff(c_167, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_161])).
% 2.22/1.32  tff(c_62, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.22/1.32  tff(c_70, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.22/1.32  tff(c_125, plain, (![B_54, A_55]: (k7_relat_1(B_54, A_55)=B_54 | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.32  tff(c_131, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_125])).
% 2.22/1.32  tff(c_137, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_131])).
% 2.22/1.32  tff(c_16, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.22/1.32  tff(c_36, plain, (![A_14, B_15]: (k5_relat_1(k6_partfun1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16])).
% 2.22/1.32  tff(c_199, plain, (![E_72, A_74, B_73, F_75, C_71, D_76]: (k4_relset_1(A_74, B_73, C_71, D_76, E_72, F_75)=k5_relat_1(E_72, F_75) | ~m1_subset_1(F_75, k1_zfmisc_1(k2_zfmisc_1(C_71, D_76))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.22/1.32  tff(c_206, plain, (![A_77, B_78, E_79]: (k4_relset_1(A_77, B_78, '#skF_1', '#skF_2', E_79, '#skF_3')=k5_relat_1(E_79, '#skF_3') | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(resolution, [status(thm)], [c_34, c_199])).
% 2.22/1.32  tff(c_213, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_35, c_206])).
% 2.22/1.32  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.22/1.32  tff(c_72, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.22/1.32  tff(c_219, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_72])).
% 2.22/1.32  tff(c_238, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_219])).
% 2.22/1.32  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_167, c_137, c_238])).
% 2.22/1.32  tff(c_242, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.22/1.32  tff(c_496, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_242])).
% 2.22/1.32  tff(c_508, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37, c_496])).
% 2.22/1.32  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_355, c_344, c_508])).
% 2.22/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  Inference rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Ref     : 0
% 2.22/1.32  #Sup     : 104
% 2.22/1.32  #Fact    : 0
% 2.22/1.32  #Define  : 0
% 2.22/1.32  #Split   : 2
% 2.22/1.32  #Chain   : 0
% 2.22/1.32  #Close   : 0
% 2.22/1.32  
% 2.22/1.32  Ordering : KBO
% 2.22/1.32  
% 2.22/1.32  Simplification rules
% 2.22/1.32  ----------------------
% 2.22/1.32  #Subsume      : 0
% 2.22/1.32  #Demod        : 58
% 2.22/1.32  #Tautology    : 60
% 2.22/1.32  #SimpNegUnit  : 0
% 2.22/1.32  #BackRed      : 5
% 2.22/1.32  
% 2.22/1.32  #Partial instantiations: 0
% 2.22/1.32  #Strategies tried      : 1
% 2.22/1.32  
% 2.22/1.32  Timing (in seconds)
% 2.22/1.32  ----------------------
% 2.22/1.33  Preprocessing        : 0.31
% 2.22/1.33  Parsing              : 0.16
% 2.22/1.33  CNF conversion       : 0.02
% 2.22/1.33  Main loop            : 0.26
% 2.22/1.33  Inferencing          : 0.11
% 2.22/1.33  Reduction            : 0.08
% 2.22/1.33  Demodulation         : 0.06
% 2.22/1.33  BG Simplification    : 0.01
% 2.22/1.33  Subsumption          : 0.03
% 2.22/1.33  Abstraction          : 0.02
% 2.22/1.33  MUC search           : 0.00
% 2.22/1.33  Cooper               : 0.00
% 2.22/1.33  Total                : 0.60
% 2.22/1.33  Index Insertion      : 0.00
% 2.22/1.33  Index Deletion       : 0.00
% 2.22/1.33  Index Matching       : 0.00
% 2.22/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
