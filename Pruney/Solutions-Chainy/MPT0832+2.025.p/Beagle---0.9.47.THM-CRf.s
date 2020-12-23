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
% DateTime   : Thu Dec  3 10:07:43 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 227 expanded)
%              Number of leaves         :   29 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 418 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_52])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k8_relat_1(A_15,B_16),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_36])).

tff(c_159,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_187,plain,(
    ! [A_71] :
      ( v1_relat_1(A_71)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_172,c_53])).

tff(c_195,plain,(
    ! [A_72] :
      ( v1_relat_1(A_72)
      | ~ r1_tarski(A_72,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_187])).

tff(c_207,plain,(
    ! [A_15] :
      ( v1_relat_1(k8_relat_1(A_15,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_195])).

tff(c_212,plain,(
    ! [A_15] : v1_relat_1(k8_relat_1(A_15,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_207])).

tff(c_82,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_90,plain,(
    ! [A_4,B_49,A_50] :
      ( v5_relat_1(A_4,B_49)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_50,B_49)) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_190,plain,(
    ! [A_71] :
      ( v5_relat_1(A_71,'#skF_1')
      | ~ r1_tarski(A_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_172,c_90])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_213,plain,(
    ! [A_73,B_74] :
      ( k8_relat_1(A_73,B_74) = B_74
      | ~ r1_tarski(k2_relat_1(B_74),A_73)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_232,plain,(
    ! [A_80,B_81] :
      ( k8_relat_1(A_80,B_81) = B_81
      | ~ v5_relat_1(B_81,A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_12,c_213])).

tff(c_348,plain,(
    ! [A_90] :
      ( k8_relat_1('#skF_1',A_90) = A_90
      | ~ v1_relat_1(A_90)
      | ~ r1_tarski(A_90,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_190,c_232])).

tff(c_363,plain,(
    ! [A_15] :
      ( k8_relat_1('#skF_1',k8_relat_1(A_15,'#skF_4')) = k8_relat_1(A_15,'#skF_4')
      | ~ v1_relat_1(k8_relat_1(A_15,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_348])).

tff(c_380,plain,(
    ! [A_95] : k8_relat_1('#skF_1',k8_relat_1(A_95,'#skF_4')) = k8_relat_1(A_95,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_212,c_363])).

tff(c_395,plain,(
    ! [A_95] :
      ( r1_tarski(k8_relat_1(A_95,'#skF_4'),k8_relat_1(A_95,'#skF_4'))
      | ~ v1_relat_1(k8_relat_1(A_95,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_18])).

tff(c_410,plain,(
    ! [A_95] : r1_tarski(k8_relat_1(A_95,'#skF_4'),k8_relat_1(A_95,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_395])).

tff(c_546,plain,(
    ! [A_103,B_104,A_105] :
      ( r1_tarski(A_103,B_104)
      | ~ r1_tarski(A_103,k8_relat_1(A_105,B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_18,c_159])).

tff(c_549,plain,(
    ! [A_95] :
      ( r1_tarski(k8_relat_1(A_95,'#skF_4'),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_410,c_546])).

tff(c_570,plain,(
    ! [A_95] : r1_tarski(k8_relat_1(A_95,'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_549])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_13,B_14)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1292,plain,(
    ! [A_181,B_182] :
      ( k8_relat_1(A_181,k8_relat_1(A_181,B_182)) = k8_relat_1(A_181,B_182)
      | ~ v1_relat_1(k8_relat_1(A_181,B_182))
      | ~ v1_relat_1(B_182) ) ),
    inference(resolution,[status(thm)],[c_16,c_213])).

tff(c_1302,plain,(
    ! [A_15] :
      ( k8_relat_1(A_15,k8_relat_1(A_15,'#skF_4')) = k8_relat_1(A_15,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_212,c_1292])).

tff(c_1319,plain,(
    ! [A_183] : k8_relat_1(A_183,k8_relat_1(A_183,'#skF_4')) = k8_relat_1(A_183,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1302])).

tff(c_1390,plain,(
    ! [A_183] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_183,'#skF_4')),A_183)
      | ~ v1_relat_1(k8_relat_1(A_183,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_16])).

tff(c_1440,plain,(
    ! [A_183] : r1_tarski(k2_relat_1(k8_relat_1(A_183,'#skF_4')),A_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_1390])).

tff(c_169,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_68,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_372,plain,(
    ! [D_91,C_92,B_93,A_94] :
      ( m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(C_92,B_93)))
      | ~ r1_tarski(k2_relat_1(D_91),B_93)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(C_92,A_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1612,plain,(
    ! [A_189,C_190,B_191,A_192] :
      ( m1_subset_1(A_189,k1_zfmisc_1(k2_zfmisc_1(C_190,B_191)))
      | ~ r1_tarski(k2_relat_1(A_189),B_191)
      | ~ r1_tarski(A_189,k2_zfmisc_1(C_190,A_192)) ) ),
    inference(resolution,[status(thm)],[c_6,c_372])).

tff(c_1673,plain,(
    ! [A_197,B_198] :
      ( m1_subset_1(A_197,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_198)))
      | ~ r1_tarski(k2_relat_1(A_197),B_198)
      | ~ r1_tarski(A_197,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_169,c_1612])).

tff(c_283,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k6_relset_1(A_82,B_83,C_84,D_85) = k8_relat_1(C_84,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_290,plain,(
    ! [C_84] : k6_relset_1('#skF_3','#skF_1',C_84,'#skF_4') = k8_relat_1(C_84,'#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_283])).

tff(c_30,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_312,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_30])).

tff(c_1678,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1673,c_312])).

tff(c_1697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_1440,c_1678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.73  
% 3.73/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.73  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.73/1.73  
% 3.73/1.73  %Foreground sorts:
% 3.73/1.73  
% 3.73/1.73  
% 3.73/1.73  %Background operators:
% 3.73/1.73  
% 3.73/1.73  
% 3.73/1.73  %Foreground operators:
% 3.73/1.73  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.73/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.73/1.73  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 3.73/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.73/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.73/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.73/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.73  
% 4.03/1.75  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.03/1.75  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 4.03/1.75  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.03/1.75  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 4.03/1.75  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.03/1.75  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.03/1.75  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.03/1.75  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.03/1.75  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 4.03/1.75  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 4.03/1.75  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 4.03/1.75  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 4.03/1.75  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.03/1.75  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.03/1.75  tff(c_46, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.03/1.75  tff(c_52, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_46])).
% 4.03/1.75  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_52])).
% 4.03/1.75  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k8_relat_1(A_15, B_16), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.03/1.75  tff(c_36, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.03/1.75  tff(c_44, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_36])).
% 4.03/1.75  tff(c_159, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.03/1.75  tff(c_172, plain, (![A_71]: (r1_tarski(A_71, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_71, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_159])).
% 4.03/1.75  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.03/1.75  tff(c_53, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_46])).
% 4.03/1.75  tff(c_187, plain, (![A_71]: (v1_relat_1(A_71) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_71, '#skF_4'))), inference(resolution, [status(thm)], [c_172, c_53])).
% 4.03/1.75  tff(c_195, plain, (![A_72]: (v1_relat_1(A_72) | ~r1_tarski(A_72, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_187])).
% 4.03/1.75  tff(c_207, plain, (![A_15]: (v1_relat_1(k8_relat_1(A_15, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_195])).
% 4.03/1.75  tff(c_212, plain, (![A_15]: (v1_relat_1(k8_relat_1(A_15, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_207])).
% 4.03/1.75  tff(c_82, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.03/1.75  tff(c_90, plain, (![A_4, B_49, A_50]: (v5_relat_1(A_4, B_49) | ~r1_tarski(A_4, k2_zfmisc_1(A_50, B_49)))), inference(resolution, [status(thm)], [c_6, c_82])).
% 4.03/1.75  tff(c_190, plain, (![A_71]: (v5_relat_1(A_71, '#skF_1') | ~r1_tarski(A_71, '#skF_4'))), inference(resolution, [status(thm)], [c_172, c_90])).
% 4.03/1.75  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.03/1.75  tff(c_213, plain, (![A_73, B_74]: (k8_relat_1(A_73, B_74)=B_74 | ~r1_tarski(k2_relat_1(B_74), A_73) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.03/1.75  tff(c_232, plain, (![A_80, B_81]: (k8_relat_1(A_80, B_81)=B_81 | ~v5_relat_1(B_81, A_80) | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_12, c_213])).
% 4.03/1.75  tff(c_348, plain, (![A_90]: (k8_relat_1('#skF_1', A_90)=A_90 | ~v1_relat_1(A_90) | ~r1_tarski(A_90, '#skF_4'))), inference(resolution, [status(thm)], [c_190, c_232])).
% 4.03/1.75  tff(c_363, plain, (![A_15]: (k8_relat_1('#skF_1', k8_relat_1(A_15, '#skF_4'))=k8_relat_1(A_15, '#skF_4') | ~v1_relat_1(k8_relat_1(A_15, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_348])).
% 4.03/1.75  tff(c_380, plain, (![A_95]: (k8_relat_1('#skF_1', k8_relat_1(A_95, '#skF_4'))=k8_relat_1(A_95, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_212, c_363])).
% 4.03/1.75  tff(c_395, plain, (![A_95]: (r1_tarski(k8_relat_1(A_95, '#skF_4'), k8_relat_1(A_95, '#skF_4')) | ~v1_relat_1(k8_relat_1(A_95, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_380, c_18])).
% 4.03/1.75  tff(c_410, plain, (![A_95]: (r1_tarski(k8_relat_1(A_95, '#skF_4'), k8_relat_1(A_95, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_395])).
% 4.03/1.75  tff(c_546, plain, (![A_103, B_104, A_105]: (r1_tarski(A_103, B_104) | ~r1_tarski(A_103, k8_relat_1(A_105, B_104)) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_18, c_159])).
% 4.03/1.75  tff(c_549, plain, (![A_95]: (r1_tarski(k8_relat_1(A_95, '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_410, c_546])).
% 4.03/1.75  tff(c_570, plain, (![A_95]: (r1_tarski(k8_relat_1(A_95, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_549])).
% 4.03/1.75  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k2_relat_1(k8_relat_1(A_13, B_14)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.03/1.75  tff(c_1292, plain, (![A_181, B_182]: (k8_relat_1(A_181, k8_relat_1(A_181, B_182))=k8_relat_1(A_181, B_182) | ~v1_relat_1(k8_relat_1(A_181, B_182)) | ~v1_relat_1(B_182))), inference(resolution, [status(thm)], [c_16, c_213])).
% 4.03/1.75  tff(c_1302, plain, (![A_15]: (k8_relat_1(A_15, k8_relat_1(A_15, '#skF_4'))=k8_relat_1(A_15, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_212, c_1292])).
% 4.03/1.75  tff(c_1319, plain, (![A_183]: (k8_relat_1(A_183, k8_relat_1(A_183, '#skF_4'))=k8_relat_1(A_183, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1302])).
% 4.03/1.75  tff(c_1390, plain, (![A_183]: (r1_tarski(k2_relat_1(k8_relat_1(A_183, '#skF_4')), A_183) | ~v1_relat_1(k8_relat_1(A_183, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1319, c_16])).
% 4.03/1.75  tff(c_1440, plain, (![A_183]: (r1_tarski(k2_relat_1(k8_relat_1(A_183, '#skF_4')), A_183))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_1390])).
% 4.03/1.75  tff(c_169, plain, (![A_68]: (r1_tarski(A_68, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_68, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_159])).
% 4.03/1.75  tff(c_372, plain, (![D_91, C_92, B_93, A_94]: (m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(C_92, B_93))) | ~r1_tarski(k2_relat_1(D_91), B_93) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(C_92, A_94))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.03/1.75  tff(c_1612, plain, (![A_189, C_190, B_191, A_192]: (m1_subset_1(A_189, k1_zfmisc_1(k2_zfmisc_1(C_190, B_191))) | ~r1_tarski(k2_relat_1(A_189), B_191) | ~r1_tarski(A_189, k2_zfmisc_1(C_190, A_192)))), inference(resolution, [status(thm)], [c_6, c_372])).
% 4.03/1.75  tff(c_1673, plain, (![A_197, B_198]: (m1_subset_1(A_197, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_198))) | ~r1_tarski(k2_relat_1(A_197), B_198) | ~r1_tarski(A_197, '#skF_4'))), inference(resolution, [status(thm)], [c_169, c_1612])).
% 4.03/1.75  tff(c_283, plain, (![A_82, B_83, C_84, D_85]: (k6_relset_1(A_82, B_83, C_84, D_85)=k8_relat_1(C_84, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.03/1.75  tff(c_290, plain, (![C_84]: (k6_relset_1('#skF_3', '#skF_1', C_84, '#skF_4')=k8_relat_1(C_84, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_283])).
% 4.03/1.75  tff(c_30, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.03/1.75  tff(c_312, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_30])).
% 4.03/1.75  tff(c_1678, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1673, c_312])).
% 4.03/1.75  tff(c_1697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_570, c_1440, c_1678])).
% 4.03/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.75  
% 4.03/1.75  Inference rules
% 4.03/1.75  ----------------------
% 4.03/1.75  #Ref     : 0
% 4.03/1.75  #Sup     : 360
% 4.03/1.75  #Fact    : 0
% 4.03/1.75  #Define  : 0
% 4.03/1.75  #Split   : 4
% 4.03/1.75  #Chain   : 0
% 4.03/1.75  #Close   : 0
% 4.03/1.75  
% 4.03/1.75  Ordering : KBO
% 4.03/1.75  
% 4.03/1.75  Simplification rules
% 4.03/1.75  ----------------------
% 4.03/1.75  #Subsume      : 51
% 4.03/1.75  #Demod        : 209
% 4.03/1.75  #Tautology    : 112
% 4.03/1.75  #SimpNegUnit  : 2
% 4.03/1.75  #BackRed      : 2
% 4.03/1.75  
% 4.03/1.75  #Partial instantiations: 0
% 4.03/1.75  #Strategies tried      : 1
% 4.03/1.75  
% 4.03/1.75  Timing (in seconds)
% 4.03/1.75  ----------------------
% 4.03/1.75  Preprocessing        : 0.38
% 4.03/1.75  Parsing              : 0.20
% 4.03/1.75  CNF conversion       : 0.02
% 4.03/1.75  Main loop            : 0.54
% 4.03/1.75  Inferencing          : 0.20
% 4.03/1.75  Reduction            : 0.18
% 4.03/1.75  Demodulation         : 0.12
% 4.03/1.75  BG Simplification    : 0.02
% 4.03/1.75  Subsumption          : 0.10
% 4.03/1.75  Abstraction          : 0.03
% 4.03/1.75  MUC search           : 0.00
% 4.03/1.75  Cooper               : 0.00
% 4.03/1.75  Total                : 0.96
% 4.03/1.75  Index Insertion      : 0.00
% 4.03/1.75  Index Deletion       : 0.00
% 4.03/1.75  Index Matching       : 0.00
% 4.03/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
