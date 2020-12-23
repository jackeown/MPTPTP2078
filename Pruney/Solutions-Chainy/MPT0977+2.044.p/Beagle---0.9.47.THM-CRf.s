%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:51 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 118 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 183 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_723,plain,(
    ! [A_150,B_151,D_152] :
      ( r2_relset_1(A_150,B_151,D_152,D_152)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_733,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_723])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_605,plain,(
    ! [B_126,A_127] :
      ( v1_relat_1(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_127))
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_614,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_605])).

tff(c_621,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_614])).

tff(c_745,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_relset_1(A_159,B_160,C_161) = k2_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_758,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_745])).

tff(c_783,plain,(
    ! [A_166,B_167,C_168] :
      ( m1_subset_1(k2_relset_1(A_166,B_167,C_168),k1_zfmisc_1(B_167))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_810,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_783])).

tff(c_820,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_810])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_828,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_820,c_2])).

tff(c_34,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_relat_1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_partfun1(A_10)) = B_11
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_831,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_828,c_40])).

tff(c_837,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_831])).

tff(c_32,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1161,plain,(
    ! [B_210,F_208,E_209,D_211,C_207,A_212] :
      ( k4_relset_1(A_212,B_210,C_207,D_211,E_209,F_208) = k5_relat_1(E_209,F_208)
      | ~ m1_subset_1(F_208,k1_zfmisc_1(k2_zfmisc_1(C_207,D_211)))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_212,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1730,plain,(
    ! [A_283,B_284,A_285,E_286] :
      ( k4_relset_1(A_283,B_284,A_285,A_285,E_286,k6_partfun1(A_285)) = k5_relat_1(E_286,k6_partfun1(A_285))
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284))) ) ),
    inference(resolution,[status(thm)],[c_32,c_1161])).

tff(c_1752,plain,(
    ! [A_285] : k4_relset_1('#skF_1','#skF_2',A_285,A_285,'#skF_3',k6_partfun1(A_285)) = k5_relat_1('#skF_3',k6_partfun1(A_285)) ),
    inference(resolution,[status(thm)],[c_38,c_1730])).

tff(c_69,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_175,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_185,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_175])).

tff(c_101,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_114,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_101])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_120,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_117])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_partfun1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_370,plain,(
    ! [F_97,C_96,D_100,A_101,B_99,E_98] :
      ( k4_relset_1(A_101,B_99,C_96,D_100,E_98,F_97) = k5_relat_1(E_98,F_97)
      | ~ m1_subset_1(F_97,k1_zfmisc_1(k2_zfmisc_1(C_96,D_100)))
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_101,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_533,plain,(
    ! [A_119,B_120,E_121] :
      ( k4_relset_1(A_119,B_120,'#skF_1','#skF_2',E_121,'#skF_3') = k5_relat_1(E_121,'#skF_3')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(resolution,[status(thm)],[c_38,c_370])).

tff(c_555,plain,(
    ! [A_33] : k4_relset_1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3') = k5_relat_1(k6_partfun1(A_33),'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_533])).

tff(c_36,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_587,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_68])).

tff(c_599,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_587])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_185,c_120,c_599])).

tff(c_603,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1753,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_603])).

tff(c_1756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_837,c_1753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:09:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.58  
% 3.39/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.59  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.39/1.59  
% 3.39/1.59  %Foreground sorts:
% 3.39/1.59  
% 3.39/1.59  
% 3.39/1.59  %Background operators:
% 3.39/1.59  
% 3.39/1.59  
% 3.39/1.59  %Foreground operators:
% 3.39/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.39/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.39/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.39/1.59  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.39/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.39/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.39/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.59  
% 3.39/1.60  tff(f_95, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 3.39/1.60  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.39/1.60  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.39/1.60  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.39/1.60  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.60  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.39/1.60  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.60  tff(f_88, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.39/1.60  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.39/1.60  tff(f_86, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.39/1.60  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.39/1.60  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.39/1.60  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.39/1.60  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.39/1.60  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.39/1.60  tff(c_723, plain, (![A_150, B_151, D_152]: (r2_relset_1(A_150, B_151, D_152, D_152) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.39/1.60  tff(c_733, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_723])).
% 3.39/1.60  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.60  tff(c_605, plain, (![B_126, A_127]: (v1_relat_1(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_127)) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.60  tff(c_614, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_605])).
% 3.39/1.60  tff(c_621, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_614])).
% 3.39/1.60  tff(c_745, plain, (![A_159, B_160, C_161]: (k2_relset_1(A_159, B_160, C_161)=k2_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.60  tff(c_758, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_745])).
% 3.39/1.60  tff(c_783, plain, (![A_166, B_167, C_168]: (m1_subset_1(k2_relset_1(A_166, B_167, C_168), k1_zfmisc_1(B_167)) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.39/1.60  tff(c_810, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_758, c_783])).
% 3.39/1.60  tff(c_820, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_810])).
% 3.39/1.60  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.60  tff(c_828, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_820, c_2])).
% 3.39/1.60  tff(c_34, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.39/1.60  tff(c_12, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_relat_1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.39/1.60  tff(c_40, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_partfun1(A_10))=B_11 | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 3.39/1.60  tff(c_831, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_828, c_40])).
% 3.39/1.60  tff(c_837, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_621, c_831])).
% 3.39/1.60  tff(c_32, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.39/1.60  tff(c_1161, plain, (![B_210, F_208, E_209, D_211, C_207, A_212]: (k4_relset_1(A_212, B_210, C_207, D_211, E_209, F_208)=k5_relat_1(E_209, F_208) | ~m1_subset_1(F_208, k1_zfmisc_1(k2_zfmisc_1(C_207, D_211))) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(A_212, B_210))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.60  tff(c_1730, plain, (![A_283, B_284, A_285, E_286]: (k4_relset_1(A_283, B_284, A_285, A_285, E_286, k6_partfun1(A_285))=k5_relat_1(E_286, k6_partfun1(A_285)) | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))))), inference(resolution, [status(thm)], [c_32, c_1161])).
% 3.39/1.60  tff(c_1752, plain, (![A_285]: (k4_relset_1('#skF_1', '#skF_2', A_285, A_285, '#skF_3', k6_partfun1(A_285))=k5_relat_1('#skF_3', k6_partfun1(A_285)))), inference(resolution, [status(thm)], [c_38, c_1730])).
% 3.39/1.60  tff(c_69, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.60  tff(c_78, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_69])).
% 3.39/1.60  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 3.39/1.60  tff(c_175, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.39/1.60  tff(c_185, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_175])).
% 3.39/1.60  tff(c_101, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.39/1.60  tff(c_114, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_101])).
% 3.39/1.60  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.39/1.60  tff(c_117, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_10])).
% 3.39/1.60  tff(c_120, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_117])).
% 3.39/1.60  tff(c_14, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.60  tff(c_39, plain, (![A_12, B_13]: (k5_relat_1(k6_partfun1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 3.39/1.60  tff(c_370, plain, (![F_97, C_96, D_100, A_101, B_99, E_98]: (k4_relset_1(A_101, B_99, C_96, D_100, E_98, F_97)=k5_relat_1(E_98, F_97) | ~m1_subset_1(F_97, k1_zfmisc_1(k2_zfmisc_1(C_96, D_100))) | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_101, B_99))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.60  tff(c_533, plain, (![A_119, B_120, E_121]: (k4_relset_1(A_119, B_120, '#skF_1', '#skF_2', E_121, '#skF_3')=k5_relat_1(E_121, '#skF_3') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(resolution, [status(thm)], [c_38, c_370])).
% 3.39/1.60  tff(c_555, plain, (![A_33]: (k4_relset_1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3')=k5_relat_1(k6_partfun1(A_33), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_533])).
% 3.39/1.60  tff(c_36, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.39/1.60  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 3.39/1.60  tff(c_587, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_68])).
% 3.39/1.60  tff(c_599, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39, c_587])).
% 3.39/1.60  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_185, c_120, c_599])).
% 3.39/1.60  tff(c_603, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.39/1.60  tff(c_1753, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1752, c_603])).
% 3.39/1.60  tff(c_1756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_733, c_837, c_1753])).
% 3.39/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.60  
% 3.39/1.60  Inference rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Ref     : 0
% 3.39/1.60  #Sup     : 357
% 3.39/1.60  #Fact    : 0
% 3.39/1.60  #Define  : 0
% 3.39/1.60  #Split   : 4
% 3.39/1.60  #Chain   : 0
% 3.39/1.60  #Close   : 0
% 3.39/1.60  
% 3.39/1.60  Ordering : KBO
% 3.39/1.60  
% 3.39/1.60  Simplification rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Subsume      : 30
% 3.39/1.60  #Demod        : 156
% 3.39/1.60  #Tautology    : 126
% 3.39/1.60  #SimpNegUnit  : 0
% 3.39/1.60  #BackRed      : 6
% 3.39/1.60  
% 3.39/1.60  #Partial instantiations: 0
% 3.39/1.60  #Strategies tried      : 1
% 3.39/1.60  
% 3.39/1.60  Timing (in seconds)
% 3.39/1.60  ----------------------
% 3.39/1.61  Preprocessing        : 0.32
% 3.39/1.61  Parsing              : 0.17
% 3.39/1.61  CNF conversion       : 0.02
% 3.39/1.61  Main loop            : 0.52
% 3.39/1.61  Inferencing          : 0.20
% 3.39/1.61  Reduction            : 0.16
% 3.39/1.61  Demodulation         : 0.12
% 3.39/1.61  BG Simplification    : 0.03
% 3.39/1.61  Subsumption          : 0.08
% 3.39/1.61  Abstraction          : 0.03
% 3.39/1.61  MUC search           : 0.00
% 3.39/1.61  Cooper               : 0.00
% 3.39/1.61  Total                : 0.87
% 3.39/1.61  Index Insertion      : 0.00
% 3.39/1.61  Index Deletion       : 0.00
% 3.39/1.61  Index Matching       : 0.00
% 3.39/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
