%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:48 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 114 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 186 expanded)
%              Number of equality atoms :   22 (  26 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_95,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_88,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_53,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_65,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_59])).

tff(c_342,plain,(
    ! [A_118,B_119,D_120] :
      ( r2_relset_1(A_118,B_119,D_120,D_120)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_348,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_342])).

tff(c_269,plain,(
    ! [C_103,B_104,A_105] :
      ( v5_relat_1(C_103,B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_277,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_269])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_279,plain,(
    ! [A_107,B_108] :
      ( k8_relat_1(A_107,B_108) = B_108
      | ~ r1_tarski(k2_relat_1(B_108),A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_284,plain,(
    ! [A_109,B_110] :
      ( k8_relat_1(A_109,B_110) = B_110
      | ~ v5_relat_1(B_110,A_109)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_10,c_279])).

tff(c_290,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_277,c_284])).

tff(c_296,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_290])).

tff(c_34,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = k8_relat_1(A_10,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_partfun1(A_10)) = k8_relat_1(A_10,B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_32,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_368,plain,(
    ! [E_127,C_126,F_130,D_131,A_129,B_128] :
      ( k4_relset_1(A_129,B_128,C_126,D_131,E_127,F_130) = k5_relat_1(E_127,F_130)
      | ~ m1_subset_1(F_130,k1_zfmisc_1(k2_zfmisc_1(C_126,D_131)))
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_439,plain,(
    ! [A_136,B_137,A_138,E_139] :
      ( k4_relset_1(A_136,B_137,A_138,A_138,E_139,k6_partfun1(A_138)) = k5_relat_1(E_139,k6_partfun1(A_138))
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(resolution,[status(thm)],[c_32,c_368])).

tff(c_445,plain,(
    ! [A_138] : k4_relset_1('#skF_1','#skF_2',A_138,A_138,'#skF_3',k6_partfun1(A_138)) = k5_relat_1('#skF_3',k6_partfun1(A_138)) ),
    inference(resolution,[status(thm)],[c_38,c_439])).

tff(c_99,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_99])).

tff(c_140,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_146,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_140])).

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

tff(c_148,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k6_partfun1(A_66),B_67) = B_67
      | ~ r1_tarski(k1_relat_1(B_67),A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_152,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_193,plain,(
    ! [D_81,B_78,F_80,E_77,C_76,A_79] :
      ( k4_relset_1(A_79,B_78,C_76,D_81,E_77,F_80) = k5_relat_1(E_77,F_80)
      | ~ m1_subset_1(F_80,k1_zfmisc_1(k2_zfmisc_1(C_76,D_81)))
      | ~ m1_subset_1(E_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_200,plain,(
    ! [A_82,B_83,E_84] :
      ( k4_relset_1(A_82,B_83,'#skF_1','#skF_2',E_84,'#skF_3') = k5_relat_1(E_84,'#skF_3')
      | ~ m1_subset_1(E_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(resolution,[status(thm)],[c_38,c_193])).

tff(c_207,plain,(
    ! [A_29] : k4_relset_1(A_29,A_29,'#skF_1','#skF_2',k6_partfun1(A_29),'#skF_3') = k5_relat_1(k6_partfun1(A_29),'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_200])).

tff(c_36,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_76,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_229,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_76])).

tff(c_241,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_229])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_107,c_146,c_241])).

tff(c_245,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_446,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_245])).

tff(c_458,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_446])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_348,c_296,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n022.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:21:10 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.74  
% 2.98/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.74  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.98/1.74  
% 2.98/1.74  %Foreground sorts:
% 2.98/1.74  
% 2.98/1.74  
% 2.98/1.74  %Background operators:
% 2.98/1.74  
% 2.98/1.74  
% 2.98/1.74  %Foreground operators:
% 2.98/1.74  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.98/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.74  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.98/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.98/1.74  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.74  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.98/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.98/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.74  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.98/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.98/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.98/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.74  
% 2.98/1.77  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.98/1.77  tff(f_95, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.98/1.77  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.98/1.77  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.98/1.77  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.98/1.77  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.98/1.77  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.98/1.77  tff(f_88, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.98/1.77  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.98/1.77  tff(f_86, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.98/1.77  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.98/1.77  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.98/1.77  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.98/1.77  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.98/1.77  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.98/1.77  tff(c_53, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.77  tff(c_59, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.98/1.77  tff(c_65, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_59])).
% 2.98/1.77  tff(c_342, plain, (![A_118, B_119, D_120]: (r2_relset_1(A_118, B_119, D_120, D_120) | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.98/1.77  tff(c_348, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_342])).
% 2.98/1.77  tff(c_269, plain, (![C_103, B_104, A_105]: (v5_relat_1(C_103, B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.77  tff(c_277, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_269])).
% 2.98/1.77  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.98/1.77  tff(c_279, plain, (![A_107, B_108]: (k8_relat_1(A_107, B_108)=B_108 | ~r1_tarski(k2_relat_1(B_108), A_107) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.98/1.77  tff(c_284, plain, (![A_109, B_110]: (k8_relat_1(A_109, B_110)=B_110 | ~v5_relat_1(B_110, A_109) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_10, c_279])).
% 2.98/1.77  tff(c_290, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_277, c_284])).
% 2.98/1.77  tff(c_296, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_290])).
% 2.98/1.77  tff(c_34, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.98/1.77  tff(c_14, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=k8_relat_1(A_10, B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.98/1.77  tff(c_40, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_partfun1(A_10))=k8_relat_1(A_10, B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 2.98/1.77  tff(c_32, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.98/1.77  tff(c_368, plain, (![E_127, C_126, F_130, D_131, A_129, B_128]: (k4_relset_1(A_129, B_128, C_126, D_131, E_127, F_130)=k5_relat_1(E_127, F_130) | ~m1_subset_1(F_130, k1_zfmisc_1(k2_zfmisc_1(C_126, D_131))) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.98/1.77  tff(c_439, plain, (![A_136, B_137, A_138, E_139]: (k4_relset_1(A_136, B_137, A_138, A_138, E_139, k6_partfun1(A_138))=k5_relat_1(E_139, k6_partfun1(A_138)) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(resolution, [status(thm)], [c_32, c_368])).
% 2.98/1.77  tff(c_445, plain, (![A_138]: (k4_relset_1('#skF_1', '#skF_2', A_138, A_138, '#skF_3', k6_partfun1(A_138))=k5_relat_1('#skF_3', k6_partfun1(A_138)))), inference(resolution, [status(thm)], [c_38, c_439])).
% 2.98/1.77  tff(c_99, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.77  tff(c_107, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_99])).
% 2.98/1.77  tff(c_140, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.98/1.77  tff(c_146, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_140])).
% 2.98/1.77  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.98/1.77  tff(c_18, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.98/1.77  tff(c_148, plain, (![A_66, B_67]: (k5_relat_1(k6_partfun1(A_66), B_67)=B_67 | ~r1_tarski(k1_relat_1(B_67), A_66) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 2.98/1.77  tff(c_152, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_148])).
% 2.98/1.77  tff(c_193, plain, (![D_81, B_78, F_80, E_77, C_76, A_79]: (k4_relset_1(A_79, B_78, C_76, D_81, E_77, F_80)=k5_relat_1(E_77, F_80) | ~m1_subset_1(F_80, k1_zfmisc_1(k2_zfmisc_1(C_76, D_81))) | ~m1_subset_1(E_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.98/1.77  tff(c_200, plain, (![A_82, B_83, E_84]: (k4_relset_1(A_82, B_83, '#skF_1', '#skF_2', E_84, '#skF_3')=k5_relat_1(E_84, '#skF_3') | ~m1_subset_1(E_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(resolution, [status(thm)], [c_38, c_193])).
% 2.98/1.77  tff(c_207, plain, (![A_29]: (k4_relset_1(A_29, A_29, '#skF_1', '#skF_2', k6_partfun1(A_29), '#skF_3')=k5_relat_1(k6_partfun1(A_29), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_200])).
% 2.98/1.77  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.98/1.77  tff(c_76, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.98/1.77  tff(c_229, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_76])).
% 2.98/1.77  tff(c_241, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_229])).
% 2.98/1.77  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_107, c_146, c_241])).
% 2.98/1.77  tff(c_245, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.98/1.77  tff(c_446, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_245])).
% 2.98/1.77  tff(c_458, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_446])).
% 2.98/1.77  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_348, c_296, c_458])).
% 2.98/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.77  
% 2.98/1.77  Inference rules
% 2.98/1.77  ----------------------
% 2.98/1.77  #Ref     : 0
% 2.98/1.77  #Sup     : 86
% 2.98/1.77  #Fact    : 0
% 2.98/1.77  #Define  : 0
% 2.98/1.77  #Split   : 2
% 2.98/1.77  #Chain   : 0
% 2.98/1.77  #Close   : 0
% 2.98/1.77  
% 2.98/1.77  Ordering : KBO
% 2.98/1.77  
% 2.98/1.77  Simplification rules
% 2.98/1.77  ----------------------
% 2.98/1.77  #Subsume      : 2
% 2.98/1.77  #Demod        : 52
% 2.98/1.77  #Tautology    : 46
% 2.98/1.77  #SimpNegUnit  : 0
% 2.98/1.77  #BackRed      : 4
% 2.98/1.77  
% 2.98/1.77  #Partial instantiations: 0
% 2.98/1.77  #Strategies tried      : 1
% 2.98/1.77  
% 2.98/1.77  Timing (in seconds)
% 2.98/1.77  ----------------------
% 2.98/1.77  Preprocessing        : 0.49
% 2.98/1.77  Parsing              : 0.24
% 2.98/1.77  CNF conversion       : 0.03
% 2.98/1.77  Main loop            : 0.45
% 2.98/1.77  Inferencing          : 0.18
% 2.98/1.77  Reduction            : 0.14
% 2.98/1.77  Demodulation         : 0.10
% 2.98/1.77  BG Simplification    : 0.03
% 2.98/1.77  Subsumption          : 0.06
% 2.98/1.77  Abstraction          : 0.03
% 2.98/1.77  MUC search           : 0.00
% 2.98/1.77  Cooper               : 0.00
% 2.98/1.77  Total                : 1.00
% 2.98/1.77  Index Insertion      : 0.00
% 2.98/1.77  Index Deletion       : 0.00
% 2.98/1.77  Index Matching       : 0.00
% 2.98/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
