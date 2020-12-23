%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:56 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 491 expanded)
%              Number of leaves         :   40 ( 181 expanded)
%              Depth                    :   18
%              Number of atoms          :  248 ( 887 expanded)
%              Number of equality atoms :   82 ( 292 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_955,plain,(
    ! [C_198,B_199,A_200] :
      ( v5_relat_1(C_198,B_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_200,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_964,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_955])).

tff(c_925,plain,(
    ! [C_185,A_186,B_187] :
      ( v1_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_934,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_925])).

tff(c_996,plain,(
    ! [B_208,A_209] :
      ( r1_tarski(k2_relat_1(B_208),A_209)
      | ~ v5_relat_1(B_208,A_209)
      | ~ v1_relat_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1020,plain,(
    ! [B_208,A_209] :
      ( k3_xboole_0(k2_relat_1(B_208),A_209) = k2_relat_1(B_208)
      | ~ v5_relat_1(B_208,A_209)
      | ~ v1_relat_1(B_208) ) ),
    inference(resolution,[status(thm)],[c_996,c_8])).

tff(c_1299,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( k8_relset_1(A_258,B_259,C_260,D_261) = k10_relat_1(C_260,D_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1306,plain,(
    ! [D_261] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_261) = k10_relat_1('#skF_3',D_261) ),
    inference(resolution,[status(thm)],[c_46,c_1299])).

tff(c_1397,plain,(
    ! [A_280,B_281,C_282,D_283] :
      ( m1_subset_1(k8_relset_1(A_280,B_281,C_282,D_283),k1_zfmisc_1(A_280))
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1429,plain,(
    ! [D_261] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_261),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_1397])).

tff(c_1440,plain,(
    ! [D_284] : m1_subset_1(k10_relat_1('#skF_3',D_284),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1429])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1451,plain,(
    ! [D_285] : r1_tarski(k10_relat_1('#skF_3',D_285),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1440,c_10])).

tff(c_1462,plain,(
    ! [D_285] : k3_xboole_0(k10_relat_1('#skF_3',D_285),'#skF_2') = k10_relat_1('#skF_3',D_285) ),
    inference(resolution,[status(thm)],[c_1451,c_8])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( k10_relat_1(B_12,k3_xboole_0(k2_relat_1(B_12),A_11)) = k10_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1465,plain,(
    ! [D_286] : k3_xboole_0(k10_relat_1('#skF_3',D_286),'#skF_2') = k10_relat_1('#skF_3',D_286) ),
    inference(resolution,[status(thm)],[c_1451,c_8])).

tff(c_1475,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_3',k3_xboole_0(k2_relat_1('#skF_3'),A_11)) = k3_xboole_0(k10_relat_1('#skF_3',A_11),'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1465])).

tff(c_2008,plain,(
    ! [A_319] : k10_relat_1('#skF_3',k3_xboole_0(k2_relat_1('#skF_3'),A_319)) = k10_relat_1('#skF_3',A_319) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_1462,c_1475])).

tff(c_2031,plain,(
    ! [A_209] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_209)
      | ~ v5_relat_1('#skF_3',A_209)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_2008])).

tff(c_2055,plain,(
    ! [A_320] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_320)
      | ~ v5_relat_1('#skF_3',A_320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_2031])).

tff(c_2061,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_964,c_2055])).

tff(c_1021,plain,(
    ! [C_210,A_211,B_212] :
      ( v4_relat_1(C_210,A_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1030,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1021])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1033,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1030,c_22])).

tff(c_1036,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_1033])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1040,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_18])).

tff(c_1044,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_1040])).

tff(c_1256,plain,(
    ! [A_250,B_251,C_252,D_253] :
      ( k7_relset_1(A_250,B_251,C_252,D_253) = k9_relat_1(C_252,D_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1263,plain,(
    ! [D_253] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_253) = k9_relat_1('#skF_3',D_253) ),
    inference(resolution,[status(thm)],[c_46,c_1256])).

tff(c_1123,plain,(
    ! [A_230,B_231,C_232] :
      ( k1_relset_1(A_230,B_231,C_232) = k1_relat_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1132,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1123])).

tff(c_497,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k7_relset_1(A_145,B_146,C_147,D_148) = k9_relat_1(C_147,D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_504,plain,(
    ! [D_148] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_148) = k9_relat_1('#skF_3',D_148) ),
    inference(resolution,[status(thm)],[c_46,c_497])).

tff(c_458,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( k8_relset_1(A_136,B_137,C_138,D_139) = k10_relat_1(C_138,D_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_465,plain,(
    ! [D_139] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_139) = k10_relat_1('#skF_3',D_139) ),
    inference(resolution,[status(thm)],[c_46,c_458])).

tff(c_277,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_286,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_277])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_91,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_287,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_91])).

tff(c_466,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_287])).

tff(c_505,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_466])).

tff(c_92,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_166,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_157])).

tff(c_137,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k2_relat_1(B_70),A_71)
      | ~ v5_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [B_70,A_71] :
      ( k3_xboole_0(k2_relat_1(B_70),A_71) = k2_relat_1(B_70)
      | ~ v5_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_137,c_8])).

tff(c_550,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( m1_subset_1(k8_relset_1(A_160,B_161,C_162,D_163),k1_zfmisc_1(A_160))
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_582,plain,(
    ! [D_139] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_139),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_550])).

tff(c_593,plain,(
    ! [D_164] : m1_subset_1(k10_relat_1('#skF_3',D_164),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_582])).

tff(c_604,plain,(
    ! [D_165] : r1_tarski(k10_relat_1('#skF_3',D_165),'#skF_2') ),
    inference(resolution,[status(thm)],[c_593,c_10])).

tff(c_615,plain,(
    ! [D_165] : k3_xboole_0(k10_relat_1('#skF_3',D_165),'#skF_2') = k10_relat_1('#skF_3',D_165) ),
    inference(resolution,[status(thm)],[c_604,c_8])).

tff(c_618,plain,(
    ! [D_166] : k3_xboole_0(k10_relat_1('#skF_3',D_166),'#skF_2') = k10_relat_1('#skF_3',D_166) ),
    inference(resolution,[status(thm)],[c_604,c_8])).

tff(c_628,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_3',k3_xboole_0(k2_relat_1('#skF_3'),A_11)) = k3_xboole_0(k10_relat_1('#skF_3',A_11),'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_618])).

tff(c_647,plain,(
    ! [A_168] : k10_relat_1('#skF_3',k3_xboole_0(k2_relat_1('#skF_3'),A_168)) = k10_relat_1('#skF_3',A_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_615,c_628])).

tff(c_670,plain,(
    ! [A_71] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_71)
      | ~ v5_relat_1('#skF_3',A_71)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_647])).

tff(c_694,plain,(
    ! [A_169] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_169)
      | ~ v5_relat_1('#skF_3',A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_670])).

tff(c_700,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_166,c_694])).

tff(c_749,plain,(
    ! [D_174,B_175,C_176,A_177] :
      ( m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(B_175,C_176)))
      | ~ r1_tarski(k1_relat_1(D_174),B_175)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_177,C_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_761,plain,(
    ! [B_178] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_178,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_178) ) ),
    inference(resolution,[status(thm)],[c_46,c_749])).

tff(c_30,plain,(
    ! [C_22,A_20,B_21] :
      ( v4_relat_1(C_22,A_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_797,plain,(
    ! [B_179] :
      ( v4_relat_1('#skF_3',B_179)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_179) ) ),
    inference(resolution,[status(thm)],[c_761,c_30])).

tff(c_807,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_797])).

tff(c_810,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_807,c_22])).

tff(c_813,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_810])).

tff(c_828,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_18])).

tff(c_832,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_828])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,k10_relat_1(B_16,k9_relat_1(B_16,A_15)))
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_870,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_24])).

tff(c_874,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_6,c_700,c_870])).

tff(c_791,plain,(
    ! [B_178] :
      ( v4_relat_1('#skF_3',B_178)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_178) ) ),
    inference(resolution,[status(thm)],[c_761,c_30])).

tff(c_888,plain,(
    v4_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_874,c_791])).

tff(c_893,plain,
    ( k7_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_888,c_22])).

tff(c_896,plain,(
    k7_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_893])).

tff(c_916,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_18])).

tff(c_920,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_916])).

tff(c_922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_920])).

tff(c_923,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1133,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_923])).

tff(c_1264,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1133])).

tff(c_1265,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_1264])).

tff(c_1308,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1265])).

tff(c_2068,plain,(
    k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_1308])).

tff(c_1574,plain,(
    ! [D_290,B_291,C_292,A_293] :
      ( m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(B_291,C_292)))
      | ~ r1_tarski(k1_relat_1(D_290),B_291)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(A_293,C_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1599,plain,(
    ! [B_295] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_295,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_295) ) ),
    inference(resolution,[status(thm)],[c_46,c_1574])).

tff(c_1716,plain,(
    ! [B_299] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_299,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_299) ) ),
    inference(resolution,[status(thm)],[c_1599,c_10])).

tff(c_1730,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1716])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1789,plain,(
    ! [A_301,B_302,A_303,D_304] :
      ( k8_relset_1(A_301,B_302,A_303,D_304) = k10_relat_1(A_303,D_304)
      | ~ r1_tarski(A_303,k2_zfmisc_1(A_301,B_302)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1299])).

tff(c_1800,plain,(
    ! [D_304] : k8_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3',D_304) = k10_relat_1('#skF_3',D_304) ),
    inference(resolution,[status(thm)],[c_1730,c_1789])).

tff(c_1585,plain,(
    ! [B_291] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_291,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_291) ) ),
    inference(resolution,[status(thm)],[c_46,c_1574])).

tff(c_1899,plain,(
    ! [A_312,B_313,C_314,D_315] :
      ( r1_tarski(k8_relset_1(A_312,B_313,C_314,D_315),A_312)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313))) ) ),
    inference(resolution,[status(thm)],[c_1397,c_10])).

tff(c_1915,plain,(
    ! [B_316,D_317] :
      ( r1_tarski(k8_relset_1(B_316,'#skF_1','#skF_3',D_317),B_316)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_316) ) ),
    inference(resolution,[status(thm)],[c_1585,c_1899])).

tff(c_1953,plain,(
    ! [D_304] :
      ( r1_tarski(k10_relat_1('#skF_3',D_304),k1_relat_1('#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1800,c_1915])).

tff(c_1969,plain,(
    ! [D_304] : r1_tarski(k10_relat_1('#skF_3',D_304),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1953])).

tff(c_1266,plain,(
    ! [D_254] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_254) = k9_relat_1('#skF_3',D_254) ),
    inference(resolution,[status(thm)],[c_46,c_1256])).

tff(c_1163,plain,(
    ! [A_235,B_236,C_237] :
      ( k2_relset_1(A_235,B_236,C_237) = k2_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1172,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1163])).

tff(c_924,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1173,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_924])).

tff(c_1272,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_1173])).

tff(c_1284,plain,
    ( r1_tarski(k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1272,c_24])).

tff(c_1288,plain,
    ( r1_tarski(k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_1284])).

tff(c_1480,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1306,c_1288])).

tff(c_1481,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1480])).

tff(c_1973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1969,c_1481])).

tff(c_1975,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1480])).

tff(c_2088,plain,(
    ! [D_321,B_322,C_323,A_324] :
      ( m1_subset_1(D_321,k1_zfmisc_1(k2_zfmisc_1(B_322,C_323)))
      | ~ r1_tarski(k1_relat_1(D_321),B_322)
      | ~ m1_subset_1(D_321,k1_zfmisc_1(k2_zfmisc_1(A_324,C_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2113,plain,(
    ! [B_326] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_326,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_326) ) ),
    inference(resolution,[status(thm)],[c_46,c_2088])).

tff(c_2149,plain,(
    ! [B_327] :
      ( v4_relat_1('#skF_3',B_327)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_327) ) ),
    inference(resolution,[status(thm)],[c_2113,c_30])).

tff(c_2159,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_2149])).

tff(c_2162,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2159,c_22])).

tff(c_2165,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_2162])).

tff(c_2169,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2165,c_18])).

tff(c_2173,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_2169])).

tff(c_2178,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2173,c_24])).

tff(c_2182,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_6,c_2061,c_2178])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2188,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2182,c_2])).

tff(c_2195,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1975,c_2188])).

tff(c_2197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2068,c_2195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.70  
% 3.95/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.70  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.95/1.70  
% 3.95/1.70  %Foreground sorts:
% 3.95/1.70  
% 3.95/1.70  
% 3.95/1.70  %Background operators:
% 3.95/1.70  
% 3.95/1.70  
% 3.95/1.70  %Foreground operators:
% 3.95/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.95/1.70  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.95/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.70  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.95/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.95/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.95/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.95/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.70  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.95/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.95/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.95/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.70  
% 3.95/1.73  tff(f_108, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.95/1.73  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.95/1.73  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.95/1.73  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.95/1.73  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.95/1.73  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.95/1.73  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 3.95/1.73  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.95/1.73  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 3.95/1.73  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.95/1.73  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.95/1.73  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.95/1.73  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.95/1.73  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.95/1.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/1.73  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.95/1.73  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.95/1.73  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_955, plain, (![C_198, B_199, A_200]: (v5_relat_1(C_198, B_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_200, B_199))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.95/1.73  tff(c_964, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_955])).
% 3.95/1.73  tff(c_925, plain, (![C_185, A_186, B_187]: (v1_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.95/1.73  tff(c_934, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_925])).
% 3.95/1.73  tff(c_996, plain, (![B_208, A_209]: (r1_tarski(k2_relat_1(B_208), A_209) | ~v5_relat_1(B_208, A_209) | ~v1_relat_1(B_208))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.73  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.73  tff(c_1020, plain, (![B_208, A_209]: (k3_xboole_0(k2_relat_1(B_208), A_209)=k2_relat_1(B_208) | ~v5_relat_1(B_208, A_209) | ~v1_relat_1(B_208))), inference(resolution, [status(thm)], [c_996, c_8])).
% 3.95/1.73  tff(c_1299, plain, (![A_258, B_259, C_260, D_261]: (k8_relset_1(A_258, B_259, C_260, D_261)=k10_relat_1(C_260, D_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.95/1.73  tff(c_1306, plain, (![D_261]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_261)=k10_relat_1('#skF_3', D_261))), inference(resolution, [status(thm)], [c_46, c_1299])).
% 3.95/1.73  tff(c_1397, plain, (![A_280, B_281, C_282, D_283]: (m1_subset_1(k8_relset_1(A_280, B_281, C_282, D_283), k1_zfmisc_1(A_280)) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.95/1.73  tff(c_1429, plain, (![D_261]: (m1_subset_1(k10_relat_1('#skF_3', D_261), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_1397])).
% 3.95/1.73  tff(c_1440, plain, (![D_284]: (m1_subset_1(k10_relat_1('#skF_3', D_284), k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1429])).
% 3.95/1.73  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.73  tff(c_1451, plain, (![D_285]: (r1_tarski(k10_relat_1('#skF_3', D_285), '#skF_2'))), inference(resolution, [status(thm)], [c_1440, c_10])).
% 3.95/1.73  tff(c_1462, plain, (![D_285]: (k3_xboole_0(k10_relat_1('#skF_3', D_285), '#skF_2')=k10_relat_1('#skF_3', D_285))), inference(resolution, [status(thm)], [c_1451, c_8])).
% 3.95/1.73  tff(c_20, plain, (![B_12, A_11]: (k10_relat_1(B_12, k3_xboole_0(k2_relat_1(B_12), A_11))=k10_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.95/1.73  tff(c_1465, plain, (![D_286]: (k3_xboole_0(k10_relat_1('#skF_3', D_286), '#skF_2')=k10_relat_1('#skF_3', D_286))), inference(resolution, [status(thm)], [c_1451, c_8])).
% 3.95/1.73  tff(c_1475, plain, (![A_11]: (k10_relat_1('#skF_3', k3_xboole_0(k2_relat_1('#skF_3'), A_11))=k3_xboole_0(k10_relat_1('#skF_3', A_11), '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1465])).
% 3.95/1.73  tff(c_2008, plain, (![A_319]: (k10_relat_1('#skF_3', k3_xboole_0(k2_relat_1('#skF_3'), A_319))=k10_relat_1('#skF_3', A_319))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_1462, c_1475])).
% 3.95/1.73  tff(c_2031, plain, (![A_209]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_209) | ~v5_relat_1('#skF_3', A_209) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1020, c_2008])).
% 3.95/1.73  tff(c_2055, plain, (![A_320]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_320) | ~v5_relat_1('#skF_3', A_320))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_2031])).
% 3.95/1.73  tff(c_2061, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_964, c_2055])).
% 3.95/1.73  tff(c_1021, plain, (![C_210, A_211, B_212]: (v4_relat_1(C_210, A_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.95/1.73  tff(c_1030, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1021])).
% 3.95/1.73  tff(c_22, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.73  tff(c_1033, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1030, c_22])).
% 3.95/1.73  tff(c_1036, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_934, c_1033])).
% 3.95/1.73  tff(c_18, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.95/1.73  tff(c_1040, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1036, c_18])).
% 3.95/1.73  tff(c_1044, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_934, c_1040])).
% 3.95/1.73  tff(c_1256, plain, (![A_250, B_251, C_252, D_253]: (k7_relset_1(A_250, B_251, C_252, D_253)=k9_relat_1(C_252, D_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.95/1.73  tff(c_1263, plain, (![D_253]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_253)=k9_relat_1('#skF_3', D_253))), inference(resolution, [status(thm)], [c_46, c_1256])).
% 3.95/1.73  tff(c_1123, plain, (![A_230, B_231, C_232]: (k1_relset_1(A_230, B_231, C_232)=k1_relat_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.95/1.73  tff(c_1132, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1123])).
% 3.95/1.73  tff(c_497, plain, (![A_145, B_146, C_147, D_148]: (k7_relset_1(A_145, B_146, C_147, D_148)=k9_relat_1(C_147, D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.95/1.73  tff(c_504, plain, (![D_148]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_148)=k9_relat_1('#skF_3', D_148))), inference(resolution, [status(thm)], [c_46, c_497])).
% 3.95/1.73  tff(c_458, plain, (![A_136, B_137, C_138, D_139]: (k8_relset_1(A_136, B_137, C_138, D_139)=k10_relat_1(C_138, D_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.95/1.73  tff(c_465, plain, (![D_139]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_139)=k10_relat_1('#skF_3', D_139))), inference(resolution, [status(thm)], [c_46, c_458])).
% 3.95/1.73  tff(c_277, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.95/1.73  tff(c_286, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_277])).
% 3.95/1.73  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.73  tff(c_91, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.95/1.73  tff(c_287, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_91])).
% 3.95/1.73  tff(c_466, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_287])).
% 3.95/1.73  tff(c_505, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_466])).
% 3.95/1.73  tff(c_92, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.95/1.73  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_92])).
% 3.95/1.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.73  tff(c_157, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.95/1.73  tff(c_166, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_157])).
% 3.95/1.73  tff(c_137, plain, (![B_70, A_71]: (r1_tarski(k2_relat_1(B_70), A_71) | ~v5_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.73  tff(c_156, plain, (![B_70, A_71]: (k3_xboole_0(k2_relat_1(B_70), A_71)=k2_relat_1(B_70) | ~v5_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_137, c_8])).
% 3.95/1.73  tff(c_550, plain, (![A_160, B_161, C_162, D_163]: (m1_subset_1(k8_relset_1(A_160, B_161, C_162, D_163), k1_zfmisc_1(A_160)) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.95/1.73  tff(c_582, plain, (![D_139]: (m1_subset_1(k10_relat_1('#skF_3', D_139), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_465, c_550])).
% 3.95/1.73  tff(c_593, plain, (![D_164]: (m1_subset_1(k10_relat_1('#skF_3', D_164), k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_582])).
% 3.95/1.73  tff(c_604, plain, (![D_165]: (r1_tarski(k10_relat_1('#skF_3', D_165), '#skF_2'))), inference(resolution, [status(thm)], [c_593, c_10])).
% 3.95/1.73  tff(c_615, plain, (![D_165]: (k3_xboole_0(k10_relat_1('#skF_3', D_165), '#skF_2')=k10_relat_1('#skF_3', D_165))), inference(resolution, [status(thm)], [c_604, c_8])).
% 3.95/1.73  tff(c_618, plain, (![D_166]: (k3_xboole_0(k10_relat_1('#skF_3', D_166), '#skF_2')=k10_relat_1('#skF_3', D_166))), inference(resolution, [status(thm)], [c_604, c_8])).
% 3.95/1.73  tff(c_628, plain, (![A_11]: (k10_relat_1('#skF_3', k3_xboole_0(k2_relat_1('#skF_3'), A_11))=k3_xboole_0(k10_relat_1('#skF_3', A_11), '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_618])).
% 3.95/1.73  tff(c_647, plain, (![A_168]: (k10_relat_1('#skF_3', k3_xboole_0(k2_relat_1('#skF_3'), A_168))=k10_relat_1('#skF_3', A_168))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_615, c_628])).
% 3.95/1.73  tff(c_670, plain, (![A_71]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_71) | ~v5_relat_1('#skF_3', A_71) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_647])).
% 3.95/1.73  tff(c_694, plain, (![A_169]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_169) | ~v5_relat_1('#skF_3', A_169))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_670])).
% 3.95/1.73  tff(c_700, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_166, c_694])).
% 3.95/1.73  tff(c_749, plain, (![D_174, B_175, C_176, A_177]: (m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(B_175, C_176))) | ~r1_tarski(k1_relat_1(D_174), B_175) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_177, C_176))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.95/1.73  tff(c_761, plain, (![B_178]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_178, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_178))), inference(resolution, [status(thm)], [c_46, c_749])).
% 3.95/1.73  tff(c_30, plain, (![C_22, A_20, B_21]: (v4_relat_1(C_22, A_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.95/1.73  tff(c_797, plain, (![B_179]: (v4_relat_1('#skF_3', B_179) | ~r1_tarski(k1_relat_1('#skF_3'), B_179))), inference(resolution, [status(thm)], [c_761, c_30])).
% 3.95/1.73  tff(c_807, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_797])).
% 3.95/1.73  tff(c_810, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_807, c_22])).
% 3.95/1.73  tff(c_813, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_810])).
% 3.95/1.73  tff(c_828, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_813, c_18])).
% 3.95/1.73  tff(c_832, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_828])).
% 3.95/1.73  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, k10_relat_1(B_16, k9_relat_1(B_16, A_15))) | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.95/1.73  tff(c_870, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_832, c_24])).
% 3.95/1.73  tff(c_874, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_6, c_700, c_870])).
% 3.95/1.73  tff(c_791, plain, (![B_178]: (v4_relat_1('#skF_3', B_178) | ~r1_tarski(k1_relat_1('#skF_3'), B_178))), inference(resolution, [status(thm)], [c_761, c_30])).
% 3.95/1.73  tff(c_888, plain, (v4_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_874, c_791])).
% 3.95/1.73  tff(c_893, plain, (k7_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_888, c_22])).
% 3.95/1.73  tff(c_896, plain, (k7_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_893])).
% 3.95/1.73  tff(c_916, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_896, c_18])).
% 3.95/1.73  tff(c_920, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_916])).
% 3.95/1.73  tff(c_922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_505, c_920])).
% 3.95/1.73  tff(c_923, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.95/1.73  tff(c_1133, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_923])).
% 3.95/1.73  tff(c_1264, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1133])).
% 3.95/1.73  tff(c_1265, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_1264])).
% 3.95/1.73  tff(c_1308, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1265])).
% 3.95/1.73  tff(c_2068, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_1308])).
% 3.95/1.73  tff(c_1574, plain, (![D_290, B_291, C_292, A_293]: (m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(B_291, C_292))) | ~r1_tarski(k1_relat_1(D_290), B_291) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(A_293, C_292))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.95/1.73  tff(c_1599, plain, (![B_295]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_295, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_295))), inference(resolution, [status(thm)], [c_46, c_1574])).
% 3.95/1.73  tff(c_1716, plain, (![B_299]: (r1_tarski('#skF_3', k2_zfmisc_1(B_299, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_3'), B_299))), inference(resolution, [status(thm)], [c_1599, c_10])).
% 3.95/1.73  tff(c_1730, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1716])).
% 3.95/1.73  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.73  tff(c_1789, plain, (![A_301, B_302, A_303, D_304]: (k8_relset_1(A_301, B_302, A_303, D_304)=k10_relat_1(A_303, D_304) | ~r1_tarski(A_303, k2_zfmisc_1(A_301, B_302)))), inference(resolution, [status(thm)], [c_12, c_1299])).
% 3.95/1.73  tff(c_1800, plain, (![D_304]: (k8_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3', D_304)=k10_relat_1('#skF_3', D_304))), inference(resolution, [status(thm)], [c_1730, c_1789])).
% 3.95/1.73  tff(c_1585, plain, (![B_291]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_291, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_291))), inference(resolution, [status(thm)], [c_46, c_1574])).
% 3.95/1.73  tff(c_1899, plain, (![A_312, B_313, C_314, D_315]: (r1_tarski(k8_relset_1(A_312, B_313, C_314, D_315), A_312) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))))), inference(resolution, [status(thm)], [c_1397, c_10])).
% 3.95/1.73  tff(c_1915, plain, (![B_316, D_317]: (r1_tarski(k8_relset_1(B_316, '#skF_1', '#skF_3', D_317), B_316) | ~r1_tarski(k1_relat_1('#skF_3'), B_316))), inference(resolution, [status(thm)], [c_1585, c_1899])).
% 3.95/1.73  tff(c_1953, plain, (![D_304]: (r1_tarski(k10_relat_1('#skF_3', D_304), k1_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1800, c_1915])).
% 3.95/1.73  tff(c_1969, plain, (![D_304]: (r1_tarski(k10_relat_1('#skF_3', D_304), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1953])).
% 3.95/1.73  tff(c_1266, plain, (![D_254]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_254)=k9_relat_1('#skF_3', D_254))), inference(resolution, [status(thm)], [c_46, c_1256])).
% 3.95/1.73  tff(c_1163, plain, (![A_235, B_236, C_237]: (k2_relset_1(A_235, B_236, C_237)=k2_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.95/1.73  tff(c_1172, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1163])).
% 3.95/1.73  tff(c_924, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.95/1.73  tff(c_1173, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_924])).
% 3.95/1.73  tff(c_1272, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1266, c_1173])).
% 3.95/1.73  tff(c_1284, plain, (r1_tarski(k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1272, c_24])).
% 3.95/1.73  tff(c_1288, plain, (r1_tarski(k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_1284])).
% 3.95/1.73  tff(c_1480, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1306, c_1288])).
% 3.95/1.73  tff(c_1481, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1480])).
% 3.95/1.73  tff(c_1973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1969, c_1481])).
% 3.95/1.73  tff(c_1975, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1480])).
% 3.95/1.73  tff(c_2088, plain, (![D_321, B_322, C_323, A_324]: (m1_subset_1(D_321, k1_zfmisc_1(k2_zfmisc_1(B_322, C_323))) | ~r1_tarski(k1_relat_1(D_321), B_322) | ~m1_subset_1(D_321, k1_zfmisc_1(k2_zfmisc_1(A_324, C_323))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.95/1.73  tff(c_2113, plain, (![B_326]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_326, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_326))), inference(resolution, [status(thm)], [c_46, c_2088])).
% 3.95/1.73  tff(c_2149, plain, (![B_327]: (v4_relat_1('#skF_3', B_327) | ~r1_tarski(k1_relat_1('#skF_3'), B_327))), inference(resolution, [status(thm)], [c_2113, c_30])).
% 3.95/1.73  tff(c_2159, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_2149])).
% 3.95/1.73  tff(c_2162, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2159, c_22])).
% 3.95/1.73  tff(c_2165, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_934, c_2162])).
% 3.95/1.73  tff(c_2169, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2165, c_18])).
% 3.95/1.73  tff(c_2173, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_934, c_2169])).
% 3.95/1.73  tff(c_2178, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2173, c_24])).
% 3.95/1.73  tff(c_2182, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_6, c_2061, c_2178])).
% 3.95/1.73  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.73  tff(c_2188, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2182, c_2])).
% 3.95/1.73  tff(c_2195, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1975, c_2188])).
% 3.95/1.73  tff(c_2197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2068, c_2195])).
% 3.95/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.73  
% 3.95/1.73  Inference rules
% 3.95/1.73  ----------------------
% 3.95/1.73  #Ref     : 0
% 3.95/1.73  #Sup     : 479
% 3.95/1.73  #Fact    : 0
% 3.95/1.73  #Define  : 0
% 3.95/1.73  #Split   : 6
% 3.95/1.73  #Chain   : 0
% 3.95/1.73  #Close   : 0
% 3.95/1.73  
% 3.95/1.73  Ordering : KBO
% 3.95/1.73  
% 3.95/1.73  Simplification rules
% 3.95/1.73  ----------------------
% 3.95/1.73  #Subsume      : 13
% 3.95/1.73  #Demod        : 191
% 3.95/1.73  #Tautology    : 211
% 3.95/1.73  #SimpNegUnit  : 3
% 3.95/1.73  #BackRed      : 16
% 3.95/1.73  
% 3.95/1.73  #Partial instantiations: 0
% 3.95/1.73  #Strategies tried      : 1
% 3.95/1.73  
% 3.95/1.73  Timing (in seconds)
% 3.95/1.73  ----------------------
% 3.95/1.73  Preprocessing        : 0.32
% 3.95/1.73  Parsing              : 0.17
% 3.95/1.73  CNF conversion       : 0.02
% 3.95/1.73  Main loop            : 0.61
% 3.95/1.73  Inferencing          : 0.24
% 3.95/1.73  Reduction            : 0.20
% 3.95/1.73  Demodulation         : 0.13
% 3.95/1.73  BG Simplification    : 0.03
% 3.95/1.73  Subsumption          : 0.10
% 3.95/1.73  Abstraction          : 0.03
% 3.95/1.73  MUC search           : 0.00
% 3.95/1.73  Cooper               : 0.00
% 3.95/1.73  Total                : 1.00
% 3.95/1.73  Index Insertion      : 0.00
% 3.95/1.73  Index Deletion       : 0.00
% 3.95/1.73  Index Matching       : 0.00
% 3.95/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
