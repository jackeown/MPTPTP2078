%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:24 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 105 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 179 expanded)
%              Number of equality atoms :   23 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_44,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_721,plain,(
    ! [B_128,A_129] :
      ( v1_relat_1(B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_129))
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_730,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_721])).

tff(c_737,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_730])).

tff(c_788,plain,(
    ! [C_140,B_141,A_142] :
      ( v5_relat_1(C_140,B_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_801,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_788])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1107,plain,(
    ! [A_184,B_185,C_186] :
      ( k2_relset_1(A_184,B_185,C_186) = k2_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1121,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1107])).

tff(c_40,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_80,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_606,plain,(
    ! [C_115,A_116,B_117,D_118] :
      ( r1_tarski(C_115,k1_relset_1(A_116,B_117,D_118))
      | ~ r1_tarski(k6_relat_1(C_115),D_118)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_706,plain,(
    ! [A_125,B_126] :
      ( r1_tarski('#skF_2',k1_relset_1(A_125,B_126,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(resolution,[status(thm)],[c_42,c_606])).

tff(c_712,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_706])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_712])).

tff(c_718,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1131,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_718])).

tff(c_1291,plain,(
    ! [C_204,A_205,B_206,D_207] :
      ( r1_tarski(C_204,k2_relset_1(A_205,B_206,D_207))
      | ~ r1_tarski(k6_relat_1(C_204),D_207)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1327,plain,(
    ! [A_210,B_211] :
      ( r1_tarski('#skF_2',k2_relset_1(A_210,B_211,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(resolution,[status(thm)],[c_42,c_1291])).

tff(c_1333,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_1327])).

tff(c_1336,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1333])).

tff(c_12,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_909,plain,(
    ! [C_159,A_160,B_161] :
      ( v4_relat_1(C_159,A_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_921,plain,(
    ! [A_28] : v4_relat_1(k6_relat_1(A_28),A_28) ),
    inference(resolution,[status(thm)],[c_34,c_909])).

tff(c_1027,plain,(
    ! [C_172,B_173,A_174] :
      ( v4_relat_1(C_172,B_173)
      | ~ v4_relat_1(C_172,A_174)
      | ~ v1_relat_1(C_172)
      | ~ r1_tarski(A_174,B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1031,plain,(
    ! [A_28,B_173] :
      ( v4_relat_1(k6_relat_1(A_28),B_173)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ r1_tarski(A_28,B_173) ) ),
    inference(resolution,[status(thm)],[c_921,c_1027])).

tff(c_1055,plain,(
    ! [A_176,B_177] :
      ( v4_relat_1(k6_relat_1(A_176),B_177)
      | ~ r1_tarski(A_176,B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1031])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1060,plain,(
    ! [A_176,B_177] :
      ( k7_relat_1(k6_relat_1(A_176),B_177) = k6_relat_1(A_176)
      | ~ v1_relat_1(k6_relat_1(A_176))
      | ~ r1_tarski(A_176,B_177) ) ),
    inference(resolution,[status(thm)],[c_1055,c_18])).

tff(c_1158,plain,(
    ! [A_189,B_190] :
      ( k7_relat_1(k6_relat_1(A_189),B_190) = k6_relat_1(A_189)
      | ~ r1_tarski(A_189,B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1060])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1168,plain,(
    ! [A_189,B_190] :
      ( k9_relat_1(k6_relat_1(A_189),B_190) = k2_relat_1(k6_relat_1(A_189))
      | ~ v1_relat_1(k6_relat_1(A_189))
      | ~ r1_tarski(A_189,B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_16])).

tff(c_1185,plain,(
    ! [A_191,B_192] :
      ( k9_relat_1(k6_relat_1(A_191),B_192) = A_191
      | ~ r1_tarski(A_191,B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24,c_1168])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_831,plain,(
    ! [A_148,B_149] :
      ( k9_relat_1(k6_relat_1(A_148),B_149) = B_149
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_841,plain,(
    ! [B_2,A_1] :
      ( k9_relat_1(k6_relat_1(B_2),A_1) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_831])).

tff(c_1198,plain,(
    ! [B_192,A_191] :
      ( B_192 = A_191
      | ~ r1_tarski(B_192,A_191)
      | ~ r1_tarski(A_191,B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1185,c_841])).

tff(c_1338,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1336,c_1198])).

tff(c_1346,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1131,c_1338])).

tff(c_1353,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1346])).

tff(c_1357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_801,c_1353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:57:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.58  
% 3.39/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.58  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.39/1.58  
% 3.39/1.58  %Foreground sorts:
% 3.39/1.58  
% 3.39/1.58  
% 3.39/1.58  %Background operators:
% 3.39/1.58  
% 3.39/1.58  
% 3.39/1.58  %Foreground operators:
% 3.39/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.39/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.39/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.39/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.39/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.39/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.58  
% 3.39/1.59  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.39/1.59  tff(f_102, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 3.39/1.59  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.39/1.59  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.39/1.59  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.39/1.59  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.59  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 3.39/1.59  tff(f_44, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.39/1.59  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.39/1.59  tff(f_85, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 3.39/1.59  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 3.39/1.59  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.39/1.59  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.39/1.59  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.59  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 3.39/1.59  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.59  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.59  tff(c_721, plain, (![B_128, A_129]: (v1_relat_1(B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(A_129)) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.59  tff(c_730, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_721])).
% 3.39/1.59  tff(c_737, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_730])).
% 3.39/1.59  tff(c_788, plain, (![C_140, B_141, A_142]: (v5_relat_1(C_140, B_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.39/1.59  tff(c_801, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_788])).
% 3.39/1.59  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.59  tff(c_1107, plain, (![A_184, B_185, C_186]: (k2_relset_1(A_184, B_185, C_186)=k2_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.39/1.59  tff(c_1121, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1107])).
% 3.39/1.59  tff(c_40, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.59  tff(c_80, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.39/1.59  tff(c_42, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.59  tff(c_606, plain, (![C_115, A_116, B_117, D_118]: (r1_tarski(C_115, k1_relset_1(A_116, B_117, D_118)) | ~r1_tarski(k6_relat_1(C_115), D_118) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.39/1.59  tff(c_706, plain, (![A_125, B_126]: (r1_tarski('#skF_2', k1_relset_1(A_125, B_126, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(resolution, [status(thm)], [c_42, c_606])).
% 3.39/1.59  tff(c_712, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_706])).
% 3.39/1.59  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_712])).
% 3.39/1.59  tff(c_718, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 3.39/1.59  tff(c_1131, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_718])).
% 3.39/1.59  tff(c_1291, plain, (![C_204, A_205, B_206, D_207]: (r1_tarski(C_204, k2_relset_1(A_205, B_206, D_207)) | ~r1_tarski(k6_relat_1(C_204), D_207) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.39/1.59  tff(c_1327, plain, (![A_210, B_211]: (r1_tarski('#skF_2', k2_relset_1(A_210, B_211, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(resolution, [status(thm)], [c_42, c_1291])).
% 3.39/1.59  tff(c_1333, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_1327])).
% 3.39/1.59  tff(c_1336, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1333])).
% 3.39/1.59  tff(c_12, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.39/1.59  tff(c_24, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.39/1.59  tff(c_34, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.39/1.59  tff(c_909, plain, (![C_159, A_160, B_161]: (v4_relat_1(C_159, A_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.39/1.59  tff(c_921, plain, (![A_28]: (v4_relat_1(k6_relat_1(A_28), A_28))), inference(resolution, [status(thm)], [c_34, c_909])).
% 3.39/1.59  tff(c_1027, plain, (![C_172, B_173, A_174]: (v4_relat_1(C_172, B_173) | ~v4_relat_1(C_172, A_174) | ~v1_relat_1(C_172) | ~r1_tarski(A_174, B_173))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.39/1.60  tff(c_1031, plain, (![A_28, B_173]: (v4_relat_1(k6_relat_1(A_28), B_173) | ~v1_relat_1(k6_relat_1(A_28)) | ~r1_tarski(A_28, B_173))), inference(resolution, [status(thm)], [c_921, c_1027])).
% 3.39/1.60  tff(c_1055, plain, (![A_176, B_177]: (v4_relat_1(k6_relat_1(A_176), B_177) | ~r1_tarski(A_176, B_177))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1031])).
% 3.39/1.60  tff(c_18, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.39/1.60  tff(c_1060, plain, (![A_176, B_177]: (k7_relat_1(k6_relat_1(A_176), B_177)=k6_relat_1(A_176) | ~v1_relat_1(k6_relat_1(A_176)) | ~r1_tarski(A_176, B_177))), inference(resolution, [status(thm)], [c_1055, c_18])).
% 3.39/1.60  tff(c_1158, plain, (![A_189, B_190]: (k7_relat_1(k6_relat_1(A_189), B_190)=k6_relat_1(A_189) | ~r1_tarski(A_189, B_190))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1060])).
% 3.39/1.60  tff(c_16, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.39/1.60  tff(c_1168, plain, (![A_189, B_190]: (k9_relat_1(k6_relat_1(A_189), B_190)=k2_relat_1(k6_relat_1(A_189)) | ~v1_relat_1(k6_relat_1(A_189)) | ~r1_tarski(A_189, B_190))), inference(superposition, [status(thm), theory('equality')], [c_1158, c_16])).
% 3.39/1.60  tff(c_1185, plain, (![A_191, B_192]: (k9_relat_1(k6_relat_1(A_191), B_192)=A_191 | ~r1_tarski(A_191, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24, c_1168])).
% 3.39/1.60  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.60  tff(c_831, plain, (![A_148, B_149]: (k9_relat_1(k6_relat_1(A_148), B_149)=B_149 | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.39/1.60  tff(c_841, plain, (![B_2, A_1]: (k9_relat_1(k6_relat_1(B_2), A_1)=A_1 | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_831])).
% 3.39/1.60  tff(c_1198, plain, (![B_192, A_191]: (B_192=A_191 | ~r1_tarski(B_192, A_191) | ~r1_tarski(A_191, B_192))), inference(superposition, [status(thm), theory('equality')], [c_1185, c_841])).
% 3.39/1.60  tff(c_1338, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1336, c_1198])).
% 3.39/1.60  tff(c_1346, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1131, c_1338])).
% 3.39/1.60  tff(c_1353, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1346])).
% 3.39/1.60  tff(c_1357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_737, c_801, c_1353])).
% 3.39/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.60  
% 3.39/1.60  Inference rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Ref     : 0
% 3.39/1.60  #Sup     : 276
% 3.39/1.60  #Fact    : 0
% 3.39/1.60  #Define  : 0
% 3.39/1.60  #Split   : 14
% 3.39/1.60  #Chain   : 0
% 3.39/1.60  #Close   : 0
% 3.39/1.60  
% 3.39/1.60  Ordering : KBO
% 3.39/1.60  
% 3.39/1.60  Simplification rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Subsume      : 7
% 3.39/1.60  #Demod        : 133
% 3.39/1.60  #Tautology    : 123
% 3.39/1.60  #SimpNegUnit  : 3
% 3.39/1.60  #BackRed      : 5
% 3.39/1.60  
% 3.39/1.60  #Partial instantiations: 0
% 3.39/1.60  #Strategies tried      : 1
% 3.39/1.60  
% 3.39/1.60  Timing (in seconds)
% 3.39/1.60  ----------------------
% 3.39/1.60  Preprocessing        : 0.33
% 3.39/1.60  Parsing              : 0.18
% 3.39/1.60  CNF conversion       : 0.02
% 3.39/1.60  Main loop            : 0.45
% 3.39/1.60  Inferencing          : 0.17
% 3.39/1.60  Reduction            : 0.14
% 3.39/1.60  Demodulation         : 0.10
% 3.39/1.60  BG Simplification    : 0.02
% 3.39/1.60  Subsumption          : 0.07
% 3.39/1.60  Abstraction          : 0.02
% 3.39/1.60  MUC search           : 0.00
% 3.39/1.60  Cooper               : 0.00
% 3.39/1.60  Total                : 0.81
% 3.39/1.60  Index Insertion      : 0.00
% 3.39/1.60  Index Deletion       : 0.00
% 3.39/1.60  Index Matching       : 0.00
% 3.39/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
