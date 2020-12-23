%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:48 EST 2020

% Result     : Theorem 4.99s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 124 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 187 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_109,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1359,plain,(
    ! [A_215,B_216,D_217] :
      ( r2_relset_1(A_215,B_216,D_217,D_217)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1369,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1359])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1129,plain,(
    ! [B_179,A_180] :
      ( v1_relat_1(B_179)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(A_180))
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1138,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_1129])).

tff(c_1145,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1138])).

tff(c_1552,plain,(
    ! [A_242,B_243,C_244] :
      ( k2_relset_1(A_242,B_243,C_244) = k2_relat_1(C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1566,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1552])).

tff(c_1719,plain,(
    ! [A_253,B_254,C_255] :
      ( m1_subset_1(k2_relset_1(A_253,B_254,C_255),k1_zfmisc_1(B_254))
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1743,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1566,c_1719])).

tff(c_1754,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1743])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1796,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1754,c_2])).

tff(c_48,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_relat_1(A_17)) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_partfun1(A_17)) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_1801,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1796,c_58])).

tff(c_1808,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_1801])).

tff(c_46,plain,(
    ! [A_41] : m1_subset_1(k6_relat_1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_53,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_2506,plain,(
    ! [C_338,B_334,A_336,F_337,E_335,D_333] :
      ( k4_relset_1(A_336,B_334,C_338,D_333,E_335,F_337) = k5_relat_1(E_335,F_337)
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1(C_338,D_333)))
      | ~ m1_subset_1(E_335,k1_zfmisc_1(k2_zfmisc_1(A_336,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3510,plain,(
    ! [A_452,B_453,A_454,E_455] :
      ( k4_relset_1(A_452,B_453,A_454,A_454,E_455,k6_partfun1(A_454)) = k5_relat_1(E_455,k6_partfun1(A_454))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453))) ) ),
    inference(resolution,[status(thm)],[c_53,c_2506])).

tff(c_3532,plain,(
    ! [A_454] : k4_relset_1('#skF_1','#skF_2',A_454,A_454,'#skF_3',k6_partfun1(A_454)) = k5_relat_1('#skF_3',k6_partfun1(A_454)) ),
    inference(resolution,[status(thm)],[c_52,c_3510])).

tff(c_109,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_118,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_109])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_452,plain,(
    ! [A_107,B_108,D_109] :
      ( r2_relset_1(A_107,B_108,D_109,D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_462,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_452])).

tff(c_184,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_198,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_184])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_216,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_198,c_14])).

tff(c_219,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_216])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_57,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_partfun1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_900,plain,(
    ! [B_152,A_154,D_151,F_155,C_156,E_153] :
      ( k4_relset_1(A_154,B_152,C_156,D_151,E_153,F_155) = k5_relat_1(E_153,F_155)
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(C_156,D_151)))
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_978,plain,(
    ! [A_160,B_161,E_162] :
      ( k4_relset_1(A_160,B_161,'#skF_1','#skF_2',E_162,'#skF_3') = k5_relat_1(E_162,'#skF_3')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(resolution,[status(thm)],[c_52,c_900])).

tff(c_1000,plain,(
    ! [A_41] : k4_relset_1(A_41,A_41,'#skF_1','#skF_2',k6_partfun1(A_41),'#skF_3') = k5_relat_1(k6_partfun1(A_41),'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_978])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_93,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1096,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_93])).

tff(c_1108,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_1096])).

tff(c_1111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_462,c_219,c_1108])).

tff(c_1112,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3612,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_1112])).

tff(c_3615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1808,c_3612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:53:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.99/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.94  
% 4.99/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.94  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.99/1.94  
% 4.99/1.94  %Foreground sorts:
% 4.99/1.94  
% 4.99/1.94  
% 4.99/1.94  %Background operators:
% 4.99/1.94  
% 4.99/1.94  
% 4.99/1.94  %Foreground operators:
% 4.99/1.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.99/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.99/1.94  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.99/1.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.99/1.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.99/1.94  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.99/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.99/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.99/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.99/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.99/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.99/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.99/1.94  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.99/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.99/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.99/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.99/1.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.99/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.99/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.99/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.99/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.99/1.94  
% 4.99/1.96  tff(f_118, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 4.99/1.96  tff(f_107, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.99/1.96  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.99/1.96  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.99/1.96  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.99/1.96  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.99/1.96  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.99/1.96  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.99/1.96  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 4.99/1.96  tff(f_109, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.99/1.96  tff(f_99, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.99/1.96  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.99/1.96  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.99/1.96  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.99/1.96  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.99/1.96  tff(c_1359, plain, (![A_215, B_216, D_217]: (r2_relset_1(A_215, B_216, D_217, D_217) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.99/1.96  tff(c_1369, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1359])).
% 4.99/1.96  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.99/1.96  tff(c_1129, plain, (![B_179, A_180]: (v1_relat_1(B_179) | ~m1_subset_1(B_179, k1_zfmisc_1(A_180)) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.99/1.96  tff(c_1138, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_1129])).
% 4.99/1.96  tff(c_1145, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1138])).
% 4.99/1.96  tff(c_1552, plain, (![A_242, B_243, C_244]: (k2_relset_1(A_242, B_243, C_244)=k2_relat_1(C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.99/1.96  tff(c_1566, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1552])).
% 4.99/1.96  tff(c_1719, plain, (![A_253, B_254, C_255]: (m1_subset_1(k2_relset_1(A_253, B_254, C_255), k1_zfmisc_1(B_254)) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.99/1.96  tff(c_1743, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1566, c_1719])).
% 4.99/1.96  tff(c_1754, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1743])).
% 4.99/1.96  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.99/1.96  tff(c_1796, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1754, c_2])).
% 4.99/1.96  tff(c_48, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.99/1.96  tff(c_22, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_relat_1(A_17))=B_18 | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.99/1.96  tff(c_58, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_partfun1(A_17))=B_18 | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 4.99/1.96  tff(c_1801, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1796, c_58])).
% 4.99/1.96  tff(c_1808, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1145, c_1801])).
% 4.99/1.96  tff(c_46, plain, (![A_41]: (m1_subset_1(k6_relat_1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.99/1.96  tff(c_53, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 4.99/1.96  tff(c_2506, plain, (![C_338, B_334, A_336, F_337, E_335, D_333]: (k4_relset_1(A_336, B_334, C_338, D_333, E_335, F_337)=k5_relat_1(E_335, F_337) | ~m1_subset_1(F_337, k1_zfmisc_1(k2_zfmisc_1(C_338, D_333))) | ~m1_subset_1(E_335, k1_zfmisc_1(k2_zfmisc_1(A_336, B_334))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.99/1.96  tff(c_3510, plain, (![A_452, B_453, A_454, E_455]: (k4_relset_1(A_452, B_453, A_454, A_454, E_455, k6_partfun1(A_454))=k5_relat_1(E_455, k6_partfun1(A_454)) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))))), inference(resolution, [status(thm)], [c_53, c_2506])).
% 4.99/1.96  tff(c_3532, plain, (![A_454]: (k4_relset_1('#skF_1', '#skF_2', A_454, A_454, '#skF_3', k6_partfun1(A_454))=k5_relat_1('#skF_3', k6_partfun1(A_454)))), inference(resolution, [status(thm)], [c_52, c_3510])).
% 4.99/1.96  tff(c_109, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.99/1.96  tff(c_118, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_109])).
% 4.99/1.96  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_118])).
% 4.99/1.96  tff(c_452, plain, (![A_107, B_108, D_109]: (r2_relset_1(A_107, B_108, D_109, D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.99/1.96  tff(c_462, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_452])).
% 4.99/1.96  tff(c_184, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.99/1.96  tff(c_198, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_184])).
% 4.99/1.96  tff(c_14, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.99/1.96  tff(c_216, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_198, c_14])).
% 4.99/1.96  tff(c_219, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_216])).
% 4.99/1.96  tff(c_24, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.99/1.96  tff(c_57, plain, (![A_19, B_20]: (k5_relat_1(k6_partfun1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 4.99/1.96  tff(c_900, plain, (![B_152, A_154, D_151, F_155, C_156, E_153]: (k4_relset_1(A_154, B_152, C_156, D_151, E_153, F_155)=k5_relat_1(E_153, F_155) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(C_156, D_151))) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_152))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.99/1.96  tff(c_978, plain, (![A_160, B_161, E_162]: (k4_relset_1(A_160, B_161, '#skF_1', '#skF_2', E_162, '#skF_3')=k5_relat_1(E_162, '#skF_3') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(resolution, [status(thm)], [c_52, c_900])).
% 4.99/1.96  tff(c_1000, plain, (![A_41]: (k4_relset_1(A_41, A_41, '#skF_1', '#skF_2', k6_partfun1(A_41), '#skF_3')=k5_relat_1(k6_partfun1(A_41), '#skF_3'))), inference(resolution, [status(thm)], [c_53, c_978])).
% 4.99/1.96  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.99/1.96  tff(c_93, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 4.99/1.96  tff(c_1096, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_93])).
% 4.99/1.96  tff(c_1108, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_57, c_1096])).
% 4.99/1.96  tff(c_1111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_462, c_219, c_1108])).
% 4.99/1.96  tff(c_1112, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 4.99/1.96  tff(c_3612, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_1112])).
% 4.99/1.96  tff(c_3615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1808, c_3612])).
% 4.99/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.96  
% 4.99/1.96  Inference rules
% 4.99/1.96  ----------------------
% 4.99/1.96  #Ref     : 0
% 4.99/1.96  #Sup     : 724
% 4.99/1.96  #Fact    : 0
% 4.99/1.96  #Define  : 0
% 4.99/1.96  #Split   : 19
% 4.99/1.96  #Chain   : 0
% 4.99/1.96  #Close   : 0
% 4.99/1.96  
% 4.99/1.96  Ordering : KBO
% 4.99/1.96  
% 4.99/1.96  Simplification rules
% 4.99/1.96  ----------------------
% 4.99/1.96  #Subsume      : 61
% 4.99/1.96  #Demod        : 410
% 4.99/1.96  #Tautology    : 248
% 4.99/1.96  #SimpNegUnit  : 0
% 4.99/1.96  #BackRed      : 4
% 4.99/1.96  
% 4.99/1.96  #Partial instantiations: 0
% 4.99/1.96  #Strategies tried      : 1
% 4.99/1.96  
% 4.99/1.96  Timing (in seconds)
% 4.99/1.96  ----------------------
% 4.99/1.96  Preprocessing        : 0.35
% 4.99/1.96  Parsing              : 0.20
% 4.99/1.96  CNF conversion       : 0.02
% 4.99/1.96  Main loop            : 0.78
% 4.99/1.96  Inferencing          : 0.29
% 4.99/1.96  Reduction            : 0.25
% 4.99/1.96  Demodulation         : 0.18
% 4.99/1.96  BG Simplification    : 0.03
% 4.99/1.96  Subsumption          : 0.14
% 4.99/1.96  Abstraction          : 0.04
% 4.99/1.96  MUC search           : 0.00
% 4.99/1.96  Cooper               : 0.00
% 4.99/1.96  Total                : 1.17
% 4.99/1.96  Index Insertion      : 0.00
% 4.99/1.96  Index Deletion       : 0.00
% 4.99/1.96  Index Matching       : 0.00
% 4.99/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
