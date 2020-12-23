%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:57 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 301 expanded)
%              Number of leaves         :   39 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          :  195 ( 547 expanded)
%              Number of equality atoms :   73 ( 175 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_81,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_90,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_1274,plain,(
    ! [C_233,A_234,B_235] :
      ( v4_relat_1(C_233,A_234)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1283,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1274])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1286,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1283,c_24])).

tff(c_1289,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1286])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1293,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_18])).

tff(c_1297,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1293])).

tff(c_1725,plain,(
    ! [A_324,B_325,C_326,D_327] :
      ( k7_relset_1(A_324,B_325,C_326,D_327) = k9_relat_1(C_326,D_327)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1732,plain,(
    ! [D_327] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_327) = k9_relat_1('#skF_3',D_327) ),
    inference(resolution,[status(thm)],[c_46,c_1725])).

tff(c_1641,plain,(
    ! [A_309,B_310,C_311,D_312] :
      ( k8_relset_1(A_309,B_310,C_311,D_312) = k10_relat_1(C_311,D_312)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1648,plain,(
    ! [D_312] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_312) = k10_relat_1('#skF_3',D_312) ),
    inference(resolution,[status(thm)],[c_46,c_1641])).

tff(c_1528,plain,(
    ! [A_286,B_287,C_288] :
      ( k1_relset_1(A_286,B_287,C_288) = k1_relat_1(C_288)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1537,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1528])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_611,plain,(
    ! [D_165,B_166,C_167,A_168] :
      ( m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(B_166,C_167)))
      | ~ r1_tarski(k1_relat_1(D_165),B_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(A_168,C_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_619,plain,(
    ! [B_169] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_169,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_169) ) ),
    inference(resolution,[status(thm)],[c_46,c_611])).

tff(c_32,plain,(
    ! [C_24,A_22,B_23] :
      ( v4_relat_1(C_24,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_655,plain,(
    ! [B_170] :
      ( v4_relat_1('#skF_3',B_170)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_170) ) ),
    inference(resolution,[status(thm)],[c_619,c_32])).

tff(c_665,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_655])).

tff(c_668,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_665,c_24])).

tff(c_671,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_668])).

tff(c_675,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_18])).

tff(c_679,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_675])).

tff(c_122,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_131,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_122])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,k10_relat_1(B_18,k9_relat_1(B_18,A_17)))
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k10_relat_1(B_12,A_11),k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_109,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_542,plain,(
    ! [B_153,A_154] :
      ( k10_relat_1(B_153,A_154) = k1_relat_1(B_153)
      | ~ r1_tarski(k1_relat_1(B_153),k10_relat_1(B_153,A_154))
      | ~ v1_relat_1(B_153) ) ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_546,plain,(
    ! [B_18] :
      ( k10_relat_1(B_18,k9_relat_1(B_18,k1_relat_1(B_18))) = k1_relat_1(B_18)
      | ~ r1_tarski(k1_relat_1(B_18),k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_26,c_542])).

tff(c_552,plain,(
    ! [B_18] :
      ( k10_relat_1(B_18,k9_relat_1(B_18,k1_relat_1(B_18))) = k1_relat_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_546])).

tff(c_684,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_552])).

tff(c_691,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_684])).

tff(c_144,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_153,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_144])).

tff(c_218,plain,(
    ! [B_86,A_87] :
      ( k7_relat_1(B_86,A_87) = B_86
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_224,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_218])).

tff(c_230,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_224])).

tff(c_235,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_18])).

tff(c_239,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_235])).

tff(c_189,plain,(
    ! [B_81,A_82] :
      ( k2_relat_1(k7_relat_1(B_81,A_82)) = k9_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_987,plain,(
    ! [B_206,A_207,A_208] :
      ( r1_tarski(k9_relat_1(B_206,A_207),A_208)
      | ~ v5_relat_1(k7_relat_1(B_206,A_207),A_208)
      | ~ v1_relat_1(k7_relat_1(B_206,A_207))
      | ~ v1_relat_1(B_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_16])).

tff(c_999,plain,(
    ! [A_208] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_2'),A_208)
      | ~ v5_relat_1('#skF_3',A_208)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_987])).

tff(c_1013,plain,(
    ! [A_209] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_209)
      | ~ v5_relat_1('#skF_3',A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_230,c_239,c_999])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1127,plain,(
    ! [A_213] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_213) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_213) ) ),
    inference(resolution,[status(thm)],[c_1013,c_8])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k10_relat_1(B_14,k3_xboole_0(k2_relat_1(B_14),A_13)) = k10_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1140,plain,(
    ! [A_213] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_213)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1127,c_22])).

tff(c_1178,plain,(
    ! [A_214] :
      ( k10_relat_1('#skF_3',A_214) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_691,c_1140])).

tff(c_1194,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_1178])).

tff(c_580,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k7_relset_1(A_156,B_157,C_158,D_159) = k9_relat_1(C_158,D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_587,plain,(
    ! [D_159] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_159) = k9_relat_1('#skF_3',D_159) ),
    inference(resolution,[status(thm)],[c_46,c_580])).

tff(c_509,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k8_relset_1(A_146,B_147,C_148,D_149) = k10_relat_1(C_148,D_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_516,plain,(
    ! [D_149] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_149) = k10_relat_1('#skF_3',D_149) ),
    inference(resolution,[status(thm)],[c_46,c_509])).

tff(c_381,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_390,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_381])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_91,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_391,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_91])).

tff(c_517,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_391])).

tff(c_588,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_517])).

tff(c_1195,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_588])).

tff(c_1198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_1195])).

tff(c_1199,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1538,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_1199])).

tff(c_1649,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1648,c_1538])).

tff(c_1733,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1732,c_1649])).

tff(c_1734,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1733])).

tff(c_1809,plain,(
    ! [D_338,B_339,C_340,A_341] :
      ( m1_subset_1(D_338,k1_zfmisc_1(k2_zfmisc_1(B_339,C_340)))
      | ~ r1_tarski(k1_relat_1(D_338),B_339)
      | ~ m1_subset_1(D_338,k1_zfmisc_1(k2_zfmisc_1(A_341,C_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1819,plain,(
    ! [B_344] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_344,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_344) ) ),
    inference(resolution,[status(thm)],[c_46,c_1809])).

tff(c_1855,plain,(
    ! [B_345] :
      ( v4_relat_1('#skF_3',B_345)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_345) ) ),
    inference(resolution,[status(thm)],[c_1819,c_32])).

tff(c_1865,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_1855])).

tff(c_1868,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1865,c_24])).

tff(c_1871,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1868])).

tff(c_1878,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_18])).

tff(c_1884,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1878])).

tff(c_1218,plain,(
    ! [B_222,A_223] :
      ( B_222 = A_223
      | ~ r1_tarski(B_222,A_223)
      | ~ r1_tarski(A_223,B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1665,plain,(
    ! [B_314,A_315] :
      ( k10_relat_1(B_314,A_315) = k1_relat_1(B_314)
      | ~ r1_tarski(k1_relat_1(B_314),k10_relat_1(B_314,A_315))
      | ~ v1_relat_1(B_314) ) ),
    inference(resolution,[status(thm)],[c_20,c_1218])).

tff(c_1669,plain,(
    ! [B_18] :
      ( k10_relat_1(B_18,k9_relat_1(B_18,k1_relat_1(B_18))) = k1_relat_1(B_18)
      | ~ r1_tarski(k1_relat_1(B_18),k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_26,c_1665])).

tff(c_1675,plain,(
    ! [B_18] :
      ( k10_relat_1(B_18,k9_relat_1(B_18,k1_relat_1(B_18))) = k1_relat_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1669])).

tff(c_1894,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1884,c_1675])).

tff(c_1903,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1894])).

tff(c_1905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1734,c_1903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:26:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.73  
% 3.82/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.74  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.82/1.74  
% 3.82/1.74  %Foreground sorts:
% 3.82/1.74  
% 3.82/1.74  
% 3.82/1.74  %Background operators:
% 3.82/1.74  
% 3.82/1.74  
% 3.82/1.74  %Foreground operators:
% 3.82/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.82/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.82/1.74  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.82/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.82/1.74  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.82/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.82/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.82/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.82/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.82/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.82/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.82/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.82/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.74  
% 4.19/1.76  tff(f_108, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 4.19/1.76  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.19/1.76  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.19/1.76  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.19/1.76  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.19/1.76  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.19/1.76  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.19/1.76  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.19/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.19/1.76  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 4.19/1.76  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 4.19/1.76  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 4.19/1.76  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.19/1.76  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.19/1.76  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 4.19/1.76  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.19/1.76  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.19/1.76  tff(c_81, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.19/1.76  tff(c_90, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_81])).
% 4.19/1.76  tff(c_1274, plain, (![C_233, A_234, B_235]: (v4_relat_1(C_233, A_234) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.19/1.76  tff(c_1283, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1274])).
% 4.19/1.76  tff(c_24, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.19/1.76  tff(c_1286, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1283, c_24])).
% 4.19/1.76  tff(c_1289, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1286])).
% 4.19/1.76  tff(c_18, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.19/1.76  tff(c_1293, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1289, c_18])).
% 4.19/1.76  tff(c_1297, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1293])).
% 4.19/1.76  tff(c_1725, plain, (![A_324, B_325, C_326, D_327]: (k7_relset_1(A_324, B_325, C_326, D_327)=k9_relat_1(C_326, D_327) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.19/1.76  tff(c_1732, plain, (![D_327]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_327)=k9_relat_1('#skF_3', D_327))), inference(resolution, [status(thm)], [c_46, c_1725])).
% 4.19/1.76  tff(c_1641, plain, (![A_309, B_310, C_311, D_312]: (k8_relset_1(A_309, B_310, C_311, D_312)=k10_relat_1(C_311, D_312) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.19/1.76  tff(c_1648, plain, (![D_312]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_312)=k10_relat_1('#skF_3', D_312))), inference(resolution, [status(thm)], [c_46, c_1641])).
% 4.19/1.76  tff(c_1528, plain, (![A_286, B_287, C_288]: (k1_relset_1(A_286, B_287, C_288)=k1_relat_1(C_288) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.19/1.76  tff(c_1537, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1528])).
% 4.19/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.76  tff(c_611, plain, (![D_165, B_166, C_167, A_168]: (m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(B_166, C_167))) | ~r1_tarski(k1_relat_1(D_165), B_166) | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(A_168, C_167))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.19/1.76  tff(c_619, plain, (![B_169]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_169, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_169))), inference(resolution, [status(thm)], [c_46, c_611])).
% 4.19/1.76  tff(c_32, plain, (![C_24, A_22, B_23]: (v4_relat_1(C_24, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.19/1.76  tff(c_655, plain, (![B_170]: (v4_relat_1('#skF_3', B_170) | ~r1_tarski(k1_relat_1('#skF_3'), B_170))), inference(resolution, [status(thm)], [c_619, c_32])).
% 4.19/1.76  tff(c_665, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_655])).
% 4.19/1.76  tff(c_668, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_665, c_24])).
% 4.19/1.76  tff(c_671, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_668])).
% 4.19/1.76  tff(c_675, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_671, c_18])).
% 4.19/1.76  tff(c_679, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_675])).
% 4.19/1.76  tff(c_122, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.19/1.76  tff(c_131, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_122])).
% 4.19/1.76  tff(c_26, plain, (![A_17, B_18]: (r1_tarski(A_17, k10_relat_1(B_18, k9_relat_1(B_18, A_17))) | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.19/1.76  tff(c_20, plain, (![B_12, A_11]: (r1_tarski(k10_relat_1(B_12, A_11), k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.19/1.76  tff(c_109, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.76  tff(c_542, plain, (![B_153, A_154]: (k10_relat_1(B_153, A_154)=k1_relat_1(B_153) | ~r1_tarski(k1_relat_1(B_153), k10_relat_1(B_153, A_154)) | ~v1_relat_1(B_153))), inference(resolution, [status(thm)], [c_20, c_109])).
% 4.19/1.76  tff(c_546, plain, (![B_18]: (k10_relat_1(B_18, k9_relat_1(B_18, k1_relat_1(B_18)))=k1_relat_1(B_18) | ~r1_tarski(k1_relat_1(B_18), k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_26, c_542])).
% 4.19/1.76  tff(c_552, plain, (![B_18]: (k10_relat_1(B_18, k9_relat_1(B_18, k1_relat_1(B_18)))=k1_relat_1(B_18) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_546])).
% 4.19/1.76  tff(c_684, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_679, c_552])).
% 4.19/1.76  tff(c_691, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_684])).
% 4.19/1.76  tff(c_144, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.19/1.76  tff(c_153, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_144])).
% 4.19/1.76  tff(c_218, plain, (![B_86, A_87]: (k7_relat_1(B_86, A_87)=B_86 | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.19/1.76  tff(c_224, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_153, c_218])).
% 4.19/1.76  tff(c_230, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_224])).
% 4.19/1.76  tff(c_235, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_230, c_18])).
% 4.19/1.76  tff(c_239, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_235])).
% 4.19/1.76  tff(c_189, plain, (![B_81, A_82]: (k2_relat_1(k7_relat_1(B_81, A_82))=k9_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.19/1.76  tff(c_16, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.19/1.76  tff(c_987, plain, (![B_206, A_207, A_208]: (r1_tarski(k9_relat_1(B_206, A_207), A_208) | ~v5_relat_1(k7_relat_1(B_206, A_207), A_208) | ~v1_relat_1(k7_relat_1(B_206, A_207)) | ~v1_relat_1(B_206))), inference(superposition, [status(thm), theory('equality')], [c_189, c_16])).
% 4.19/1.76  tff(c_999, plain, (![A_208]: (r1_tarski(k9_relat_1('#skF_3', '#skF_2'), A_208) | ~v5_relat_1('#skF_3', A_208) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_987])).
% 4.19/1.76  tff(c_1013, plain, (![A_209]: (r1_tarski(k2_relat_1('#skF_3'), A_209) | ~v5_relat_1('#skF_3', A_209))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_230, c_239, c_999])).
% 4.19/1.76  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.19/1.76  tff(c_1127, plain, (![A_213]: (k3_xboole_0(k2_relat_1('#skF_3'), A_213)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_213))), inference(resolution, [status(thm)], [c_1013, c_8])).
% 4.19/1.76  tff(c_22, plain, (![B_14, A_13]: (k10_relat_1(B_14, k3_xboole_0(k2_relat_1(B_14), A_13))=k10_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.19/1.76  tff(c_1140, plain, (![A_213]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_213) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_213))), inference(superposition, [status(thm), theory('equality')], [c_1127, c_22])).
% 4.19/1.76  tff(c_1178, plain, (![A_214]: (k10_relat_1('#skF_3', A_214)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_214))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_691, c_1140])).
% 4.19/1.76  tff(c_1194, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_1178])).
% 4.19/1.76  tff(c_580, plain, (![A_156, B_157, C_158, D_159]: (k7_relset_1(A_156, B_157, C_158, D_159)=k9_relat_1(C_158, D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.19/1.76  tff(c_587, plain, (![D_159]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_159)=k9_relat_1('#skF_3', D_159))), inference(resolution, [status(thm)], [c_46, c_580])).
% 4.19/1.76  tff(c_509, plain, (![A_146, B_147, C_148, D_149]: (k8_relset_1(A_146, B_147, C_148, D_149)=k10_relat_1(C_148, D_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.19/1.76  tff(c_516, plain, (![D_149]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_149)=k10_relat_1('#skF_3', D_149))), inference(resolution, [status(thm)], [c_46, c_509])).
% 4.19/1.76  tff(c_381, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.19/1.76  tff(c_390, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_381])).
% 4.19/1.76  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.19/1.76  tff(c_91, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 4.19/1.76  tff(c_391, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_91])).
% 4.19/1.76  tff(c_517, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_391])).
% 4.19/1.76  tff(c_588, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_587, c_517])).
% 4.19/1.76  tff(c_1195, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_588])).
% 4.19/1.76  tff(c_1198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_679, c_1195])).
% 4.19/1.76  tff(c_1199, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 4.19/1.76  tff(c_1538, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1537, c_1199])).
% 4.19/1.76  tff(c_1649, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1648, c_1538])).
% 4.19/1.76  tff(c_1733, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1732, c_1649])).
% 4.19/1.76  tff(c_1734, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1733])).
% 4.19/1.76  tff(c_1809, plain, (![D_338, B_339, C_340, A_341]: (m1_subset_1(D_338, k1_zfmisc_1(k2_zfmisc_1(B_339, C_340))) | ~r1_tarski(k1_relat_1(D_338), B_339) | ~m1_subset_1(D_338, k1_zfmisc_1(k2_zfmisc_1(A_341, C_340))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.19/1.76  tff(c_1819, plain, (![B_344]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_344, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_344))), inference(resolution, [status(thm)], [c_46, c_1809])).
% 4.19/1.76  tff(c_1855, plain, (![B_345]: (v4_relat_1('#skF_3', B_345) | ~r1_tarski(k1_relat_1('#skF_3'), B_345))), inference(resolution, [status(thm)], [c_1819, c_32])).
% 4.19/1.76  tff(c_1865, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_1855])).
% 4.19/1.76  tff(c_1868, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1865, c_24])).
% 4.19/1.76  tff(c_1871, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1868])).
% 4.19/1.76  tff(c_1878, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1871, c_18])).
% 4.19/1.76  tff(c_1884, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1878])).
% 4.19/1.76  tff(c_1218, plain, (![B_222, A_223]: (B_222=A_223 | ~r1_tarski(B_222, A_223) | ~r1_tarski(A_223, B_222))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.19/1.76  tff(c_1665, plain, (![B_314, A_315]: (k10_relat_1(B_314, A_315)=k1_relat_1(B_314) | ~r1_tarski(k1_relat_1(B_314), k10_relat_1(B_314, A_315)) | ~v1_relat_1(B_314))), inference(resolution, [status(thm)], [c_20, c_1218])).
% 4.19/1.76  tff(c_1669, plain, (![B_18]: (k10_relat_1(B_18, k9_relat_1(B_18, k1_relat_1(B_18)))=k1_relat_1(B_18) | ~r1_tarski(k1_relat_1(B_18), k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_26, c_1665])).
% 4.19/1.76  tff(c_1675, plain, (![B_18]: (k10_relat_1(B_18, k9_relat_1(B_18, k1_relat_1(B_18)))=k1_relat_1(B_18) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1669])).
% 4.19/1.76  tff(c_1894, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1884, c_1675])).
% 4.19/1.76  tff(c_1903, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1894])).
% 4.19/1.76  tff(c_1905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1734, c_1903])).
% 4.19/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.76  
% 4.19/1.76  Inference rules
% 4.19/1.76  ----------------------
% 4.19/1.76  #Ref     : 0
% 4.19/1.76  #Sup     : 399
% 4.19/1.76  #Fact    : 0
% 4.19/1.76  #Define  : 0
% 4.19/1.76  #Split   : 7
% 4.19/1.76  #Chain   : 0
% 4.19/1.76  #Close   : 0
% 4.19/1.76  
% 4.19/1.76  Ordering : KBO
% 4.19/1.76  
% 4.19/1.76  Simplification rules
% 4.19/1.76  ----------------------
% 4.19/1.76  #Subsume      : 15
% 4.19/1.76  #Demod        : 215
% 4.19/1.76  #Tautology    : 179
% 4.19/1.76  #SimpNegUnit  : 1
% 4.19/1.76  #BackRed      : 10
% 4.19/1.76  
% 4.19/1.76  #Partial instantiations: 0
% 4.19/1.76  #Strategies tried      : 1
% 4.19/1.76  
% 4.19/1.76  Timing (in seconds)
% 4.19/1.76  ----------------------
% 4.19/1.76  Preprocessing        : 0.32
% 4.19/1.76  Parsing              : 0.17
% 4.19/1.76  CNF conversion       : 0.02
% 4.19/1.76  Main loop            : 0.56
% 4.19/1.76  Inferencing          : 0.22
% 4.19/1.76  Reduction            : 0.17
% 4.19/1.76  Demodulation         : 0.12
% 4.19/1.76  BG Simplification    : 0.03
% 4.19/1.76  Subsumption          : 0.09
% 4.19/1.76  Abstraction          : 0.03
% 4.19/1.76  MUC search           : 0.00
% 4.19/1.76  Cooper               : 0.00
% 4.19/1.76  Total                : 0.92
% 4.19/1.76  Index Insertion      : 0.00
% 4.19/1.76  Index Deletion       : 0.00
% 4.19/1.76  Index Matching       : 0.00
% 4.19/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
