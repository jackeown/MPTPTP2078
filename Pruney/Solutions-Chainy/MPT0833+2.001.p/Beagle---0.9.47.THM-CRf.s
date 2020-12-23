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
% DateTime   : Thu Dec  3 10:07:45 EST 2020

% Result     : Theorem 5.45s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 113 expanded)
%              Number of leaves         :   39 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 166 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(C,B)
     => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1570,plain,(
    ! [A_229,B_230,D_231] :
      ( r2_relset_1(A_229,B_230,D_231,D_231)
      | ~ m1_subset_1(D_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1580,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1570])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_265,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k1_xboole_0
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_287,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_265])).

tff(c_354,plain,(
    ! [A_96,C_97,B_98] :
      ( r1_xboole_0(A_96,k4_xboole_0(C_97,B_98))
      | ~ r1_tarski(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_368,plain,(
    ! [A_100,A_101] :
      ( r1_xboole_0(A_100,k1_xboole_0)
      | ~ r1_tarski(A_100,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_354])).

tff(c_385,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_368])).

tff(c_730,plain,(
    ! [A_141,B_142,C_143] :
      ( r1_tarski(A_141,B_142)
      | ~ r1_xboole_0(A_141,C_143)
      | ~ r1_tarski(A_141,k2_xboole_0(B_142,C_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_761,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(A_144,A_144)
      | ~ r1_xboole_0(A_144,B_145) ) ),
    inference(resolution,[status(thm)],[c_14,c_730])).

tff(c_769,plain,(
    ! [A_146] : r1_tarski(A_146,A_146) ),
    inference(resolution,[status(thm)],[c_385,c_761])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_391,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_403,plain,(
    ! [A_20,A_104,B_105] :
      ( v1_relat_1(A_20)
      | ~ r1_tarski(A_20,k2_zfmisc_1(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_24,c_391])).

tff(c_799,plain,(
    ! [A_104,B_105] : v1_relat_1(k2_zfmisc_1(A_104,B_105)) ),
    inference(resolution,[status(thm)],[c_769,c_403])).

tff(c_339,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_350,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_339])).

tff(c_353,plain,(
    ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_353])).

tff(c_807,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_1750,plain,(
    ! [A_247,B_248,C_249] :
      ( k2_relset_1(A_247,B_248,C_249) = k2_relat_1(C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1763,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1750])).

tff(c_2075,plain,(
    ! [A_268,B_269,C_270] :
      ( m1_subset_1(k2_relset_1(A_268,B_269,C_270),k1_zfmisc_1(B_269))
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2097,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_2075])).

tff(c_2108,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2097])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2121,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2108,c_22])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2135,plain,(
    k4_xboole_0(k2_relat_1('#skF_4'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2121,c_6])).

tff(c_2306,plain,(
    ! [A_282,B_283,C_284] :
      ( k2_xboole_0(k4_xboole_0(A_282,B_283),k3_xboole_0(A_282,k4_xboole_0(B_283,C_284))) = k4_xboole_0(A_282,C_284)
      | ~ r1_tarski(C_284,B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2847,plain,(
    ! [A_316,B_317,C_318] :
      ( r1_tarski(k4_xboole_0(A_316,B_317),k4_xboole_0(A_316,C_318))
      | ~ r1_tarski(C_318,B_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2306,c_14])).

tff(c_4889,plain,(
    ! [B_380] :
      ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_4'),B_380),k1_xboole_0)
      | ~ r1_tarski('#skF_2',B_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2135,c_2847])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4960,plain,(
    ! [B_383] :
      ( k4_xboole_0(k2_relat_1('#skF_4'),B_383) = k1_xboole_0
      | ~ r1_tarski('#skF_2',B_383) ) ),
    inference(resolution,[status(thm)],[c_4889,c_8])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1204,plain,(
    ! [A_196,B_197] :
      ( k8_relat_1(A_196,B_197) = B_197
      | ~ r1_tarski(k2_relat_1(B_197),A_196)
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1232,plain,(
    ! [B_5,B_197] :
      ( k8_relat_1(B_5,B_197) = B_197
      | ~ v1_relat_1(B_197)
      | k4_xboole_0(k2_relat_1(B_197),B_5) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1204])).

tff(c_4977,plain,(
    ! [B_383] :
      ( k8_relat_1(B_383,'#skF_4') = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4960,c_1232])).

tff(c_5136,plain,(
    ! [B_384] :
      ( k8_relat_1(B_384,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',B_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_4977])).

tff(c_5216,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_5136])).

tff(c_2212,plain,(
    ! [A_271,B_272,C_273,D_274] :
      ( k6_relset_1(A_271,B_272,C_273,D_274) = k8_relat_1(C_273,D_274)
      | ~ m1_subset_1(D_274,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2226,plain,(
    ! [C_273] : k6_relset_1('#skF_1','#skF_2',C_273,'#skF_4') = k8_relat_1(C_273,'#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2212])).

tff(c_48,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2237,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2226,c_48])).

tff(c_5217,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5216,c_2237])).

tff(c_5220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1580,c_5217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.45/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.18  
% 5.45/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.18  %$ r2_relset_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.45/2.18  
% 5.45/2.18  %Foreground sorts:
% 5.45/2.18  
% 5.45/2.18  
% 5.45/2.18  %Background operators:
% 5.45/2.18  
% 5.45/2.18  
% 5.45/2.18  %Foreground operators:
% 5.45/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.45/2.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.45/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.45/2.18  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.45/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.45/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.45/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.45/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.45/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.45/2.18  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 5.45/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.45/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.45/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.45/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.45/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.45/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.45/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.45/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.45/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.45/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.45/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.45/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.45/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.45/2.18  
% 5.45/2.20  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 5.45/2.20  tff(f_114, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.45/2.20  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.45/2.20  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.45/2.20  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.45/2.20  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 5.45/2.20  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.45/2.20  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 5.45/2.20  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.45/2.20  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.45/2.20  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.45/2.20  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.45/2.20  tff(f_29, axiom, (![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 5.45/2.20  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.45/2.20  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 5.45/2.20  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 5.45/2.20  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.45/2.20  tff(c_1570, plain, (![A_229, B_230, D_231]: (r2_relset_1(A_229, B_230, D_231, D_231) | ~m1_subset_1(D_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.45/2.20  tff(c_1580, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1570])).
% 5.45/2.20  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.45/2.20  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.45/2.20  tff(c_20, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.45/2.20  tff(c_56, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.20  tff(c_64, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_20, c_56])).
% 5.45/2.20  tff(c_265, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k1_xboole_0 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.45/2.20  tff(c_287, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_265])).
% 5.45/2.20  tff(c_354, plain, (![A_96, C_97, B_98]: (r1_xboole_0(A_96, k4_xboole_0(C_97, B_98)) | ~r1_tarski(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.45/2.20  tff(c_368, plain, (![A_100, A_101]: (r1_xboole_0(A_100, k1_xboole_0) | ~r1_tarski(A_100, A_101))), inference(superposition, [status(thm), theory('equality')], [c_287, c_354])).
% 5.45/2.20  tff(c_385, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_368])).
% 5.45/2.20  tff(c_730, plain, (![A_141, B_142, C_143]: (r1_tarski(A_141, B_142) | ~r1_xboole_0(A_141, C_143) | ~r1_tarski(A_141, k2_xboole_0(B_142, C_143)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.45/2.20  tff(c_761, plain, (![A_144, B_145]: (r1_tarski(A_144, A_144) | ~r1_xboole_0(A_144, B_145))), inference(resolution, [status(thm)], [c_14, c_730])).
% 5.45/2.20  tff(c_769, plain, (![A_146]: (r1_tarski(A_146, A_146))), inference(resolution, [status(thm)], [c_385, c_761])).
% 5.45/2.20  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.20  tff(c_391, plain, (![C_103, A_104, B_105]: (v1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.45/2.20  tff(c_403, plain, (![A_20, A_104, B_105]: (v1_relat_1(A_20) | ~r1_tarski(A_20, k2_zfmisc_1(A_104, B_105)))), inference(resolution, [status(thm)], [c_24, c_391])).
% 5.45/2.20  tff(c_799, plain, (![A_104, B_105]: (v1_relat_1(k2_zfmisc_1(A_104, B_105)))), inference(resolution, [status(thm)], [c_769, c_403])).
% 5.45/2.20  tff(c_339, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.45/2.20  tff(c_350, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_339])).
% 5.45/2.20  tff(c_353, plain, (~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_350])).
% 5.45/2.20  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_799, c_353])).
% 5.45/2.20  tff(c_807, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_350])).
% 5.45/2.20  tff(c_1750, plain, (![A_247, B_248, C_249]: (k2_relset_1(A_247, B_248, C_249)=k2_relat_1(C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.45/2.20  tff(c_1763, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1750])).
% 5.45/2.20  tff(c_2075, plain, (![A_268, B_269, C_270]: (m1_subset_1(k2_relset_1(A_268, B_269, C_270), k1_zfmisc_1(B_269)) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.45/2.20  tff(c_2097, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1763, c_2075])).
% 5.45/2.20  tff(c_2108, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2097])).
% 5.45/2.20  tff(c_22, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.20  tff(c_2121, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_2108, c_22])).
% 5.45/2.20  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k1_xboole_0 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.45/2.20  tff(c_2135, plain, (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2121, c_6])).
% 5.45/2.20  tff(c_2306, plain, (![A_282, B_283, C_284]: (k2_xboole_0(k4_xboole_0(A_282, B_283), k3_xboole_0(A_282, k4_xboole_0(B_283, C_284)))=k4_xboole_0(A_282, C_284) | ~r1_tarski(C_284, B_283))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.45/2.20  tff(c_2847, plain, (![A_316, B_317, C_318]: (r1_tarski(k4_xboole_0(A_316, B_317), k4_xboole_0(A_316, C_318)) | ~r1_tarski(C_318, B_317))), inference(superposition, [status(thm), theory('equality')], [c_2306, c_14])).
% 5.45/2.20  tff(c_4889, plain, (![B_380]: (r1_tarski(k4_xboole_0(k2_relat_1('#skF_4'), B_380), k1_xboole_0) | ~r1_tarski('#skF_2', B_380))), inference(superposition, [status(thm), theory('equality')], [c_2135, c_2847])).
% 5.45/2.20  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.45/2.20  tff(c_4960, plain, (![B_383]: (k4_xboole_0(k2_relat_1('#skF_4'), B_383)=k1_xboole_0 | ~r1_tarski('#skF_2', B_383))), inference(resolution, [status(thm)], [c_4889, c_8])).
% 5.45/2.20  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.45/2.20  tff(c_1204, plain, (![A_196, B_197]: (k8_relat_1(A_196, B_197)=B_197 | ~r1_tarski(k2_relat_1(B_197), A_196) | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.45/2.20  tff(c_1232, plain, (![B_5, B_197]: (k8_relat_1(B_5, B_197)=B_197 | ~v1_relat_1(B_197) | k4_xboole_0(k2_relat_1(B_197), B_5)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1204])).
% 5.45/2.20  tff(c_4977, plain, (![B_383]: (k8_relat_1(B_383, '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_383))), inference(superposition, [status(thm), theory('equality')], [c_4960, c_1232])).
% 5.45/2.20  tff(c_5136, plain, (![B_384]: (k8_relat_1(B_384, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', B_384))), inference(demodulation, [status(thm), theory('equality')], [c_807, c_4977])).
% 5.45/2.20  tff(c_5216, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_5136])).
% 5.45/2.20  tff(c_2212, plain, (![A_271, B_272, C_273, D_274]: (k6_relset_1(A_271, B_272, C_273, D_274)=k8_relat_1(C_273, D_274) | ~m1_subset_1(D_274, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.45/2.20  tff(c_2226, plain, (![C_273]: (k6_relset_1('#skF_1', '#skF_2', C_273, '#skF_4')=k8_relat_1(C_273, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_2212])).
% 5.45/2.20  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.45/2.20  tff(c_2237, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2226, c_48])).
% 5.45/2.20  tff(c_5217, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5216, c_2237])).
% 5.45/2.20  tff(c_5220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1580, c_5217])).
% 5.45/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.20  
% 5.45/2.20  Inference rules
% 5.45/2.20  ----------------------
% 5.45/2.20  #Ref     : 0
% 5.45/2.20  #Sup     : 1155
% 5.45/2.20  #Fact    : 0
% 5.45/2.20  #Define  : 0
% 5.45/2.20  #Split   : 13
% 5.45/2.20  #Chain   : 0
% 5.45/2.20  #Close   : 0
% 5.45/2.20  
% 5.45/2.20  Ordering : KBO
% 5.45/2.20  
% 5.45/2.20  Simplification rules
% 5.45/2.20  ----------------------
% 5.45/2.20  #Subsume      : 125
% 5.45/2.20  #Demod        : 622
% 5.45/2.20  #Tautology    : 544
% 5.45/2.20  #SimpNegUnit  : 20
% 5.45/2.20  #BackRed      : 8
% 5.45/2.20  
% 5.45/2.20  #Partial instantiations: 0
% 5.45/2.20  #Strategies tried      : 1
% 5.45/2.20  
% 5.45/2.20  Timing (in seconds)
% 5.45/2.20  ----------------------
% 5.45/2.20  Preprocessing        : 0.35
% 5.45/2.20  Parsing              : 0.19
% 5.45/2.20  CNF conversion       : 0.02
% 5.45/2.20  Main loop            : 1.01
% 5.45/2.20  Inferencing          : 0.32
% 5.45/2.20  Reduction            : 0.36
% 5.45/2.20  Demodulation         : 0.26
% 5.45/2.20  BG Simplification    : 0.04
% 5.45/2.20  Subsumption          : 0.20
% 5.45/2.20  Abstraction          : 0.04
% 5.45/2.20  MUC search           : 0.00
% 5.45/2.20  Cooper               : 0.00
% 5.45/2.20  Total                : 1.40
% 5.45/2.20  Index Insertion      : 0.00
% 5.45/2.20  Index Deletion       : 0.00
% 5.45/2.20  Index Matching       : 0.00
% 5.45/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
