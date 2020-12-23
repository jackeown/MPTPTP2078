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
% DateTime   : Thu Dec  3 10:14:52 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 295 expanded)
%              Number of leaves         :   43 ( 120 expanded)
%              Depth                    :    9
%              Number of atoms          :  156 ( 665 expanded)
%              Number of equality atoms :   85 ( 228 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_165,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_178,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,A_17),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_186,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_178,c_42])).

tff(c_198,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1889,plain,(
    ! [B_238,A_239] :
      ( k1_tarski(k1_funct_1(B_238,A_239)) = k2_relat_1(B_238)
      | k1_tarski(A_239) != k1_relat_1(B_238)
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1916,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_56])).

tff(c_1922,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_64,c_1916])).

tff(c_1951,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1922])).

tff(c_245,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_258,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_245])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_269,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_258,c_38])).

tff(c_272,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_269])).

tff(c_44,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_318,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_44])).

tff(c_322,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_318])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1989,plain,(
    ! [A_260,B_261,C_262,D_263] :
      ( k1_enumset1(A_260,B_261,C_262) = D_263
      | k2_tarski(A_260,C_262) = D_263
      | k2_tarski(B_261,C_262) = D_263
      | k2_tarski(A_260,B_261) = D_263
      | k1_tarski(C_262) = D_263
      | k1_tarski(B_261) = D_263
      | k1_tarski(A_260) = D_263
      | k1_xboole_0 = D_263
      | ~ r1_tarski(D_263,k1_enumset1(A_260,B_261,C_262)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2008,plain,(
    ! [A_2,B_3,D_263] :
      ( k1_enumset1(A_2,A_2,B_3) = D_263
      | k2_tarski(A_2,B_3) = D_263
      | k2_tarski(A_2,B_3) = D_263
      | k2_tarski(A_2,A_2) = D_263
      | k1_tarski(B_3) = D_263
      | k1_tarski(A_2) = D_263
      | k1_tarski(A_2) = D_263
      | k1_xboole_0 = D_263
      | ~ r1_tarski(D_263,k2_tarski(A_2,B_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1989])).

tff(c_2104,plain,(
    ! [A_290,B_291,D_292] :
      ( k2_tarski(A_290,B_291) = D_292
      | k2_tarski(A_290,B_291) = D_292
      | k2_tarski(A_290,B_291) = D_292
      | k1_tarski(A_290) = D_292
      | k1_tarski(B_291) = D_292
      | k1_tarski(A_290) = D_292
      | k1_tarski(A_290) = D_292
      | k1_xboole_0 = D_292
      | ~ r1_tarski(D_292,k2_tarski(A_290,B_291)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_2008])).

tff(c_2130,plain,(
    ! [A_1,D_292] :
      ( k2_tarski(A_1,A_1) = D_292
      | k2_tarski(A_1,A_1) = D_292
      | k2_tarski(A_1,A_1) = D_292
      | k1_tarski(A_1) = D_292
      | k1_tarski(A_1) = D_292
      | k1_tarski(A_1) = D_292
      | k1_tarski(A_1) = D_292
      | k1_xboole_0 = D_292
      | ~ r1_tarski(D_292,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2104])).

tff(c_2381,plain,(
    ! [A_333,D_334] :
      ( k1_tarski(A_333) = D_334
      | k1_tarski(A_333) = D_334
      | k1_tarski(A_333) = D_334
      | k1_tarski(A_333) = D_334
      | k1_tarski(A_333) = D_334
      | k1_tarski(A_333) = D_334
      | k1_tarski(A_333) = D_334
      | k1_xboole_0 = D_334
      | ~ r1_tarski(D_334,k1_tarski(A_333)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_2,c_2130])).

tff(c_2394,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_322,c_2381])).

tff(c_2411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_1951,c_1951,c_1951,c_1951,c_1951,c_1951,c_1951,c_2394])).

tff(c_2413,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1922])).

tff(c_2420,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2413,c_60])).

tff(c_54,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k7_relset_1(A_33,B_34,C_35,D_36) = k9_relat_1(C_35,D_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2491,plain,(
    ! [D_36] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_36) = k9_relat_1('#skF_4',D_36) ),
    inference(resolution,[status(thm)],[c_2420,c_54])).

tff(c_2412,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1922])).

tff(c_2630,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2413,c_2412])).

tff(c_2632,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2491,c_2630])).

tff(c_2650,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_2632])).

tff(c_2654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_2650])).

tff(c_2655,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_26,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_98,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_2659,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2655,c_98])).

tff(c_36,plain,(
    ! [A_19] : k9_relat_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2661,plain,(
    ! [A_19] : k9_relat_1('#skF_4',A_19) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2655,c_2655,c_36])).

tff(c_2662,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2655,c_26])).

tff(c_2900,plain,(
    ! [A_409,B_410,C_411,D_412] :
      ( k7_relset_1(A_409,B_410,C_411,D_412) = k9_relat_1(C_411,D_412)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2903,plain,(
    ! [A_409,B_410,D_412] : k7_relset_1(A_409,B_410,'#skF_4',D_412) = k9_relat_1('#skF_4',D_412) ),
    inference(resolution,[status(thm)],[c_2662,c_2900])).

tff(c_2908,plain,(
    ! [A_409,B_410,D_412] : k7_relset_1(A_409,B_410,'#skF_4',D_412) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_2903])).

tff(c_2910,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2908,c_56])).

tff(c_2913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2659,c_2910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/2.05  
% 5.06/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/2.05  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.06/2.05  
% 5.06/2.05  %Foreground sorts:
% 5.06/2.05  
% 5.06/2.05  
% 5.06/2.05  %Background operators:
% 5.06/2.05  
% 5.06/2.05  
% 5.06/2.05  %Foreground operators:
% 5.06/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.06/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.06/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.06/2.05  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.06/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.06/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.06/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.06/2.05  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.06/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.06/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.06/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.06/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.06/2.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.06/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.06/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.06/2.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.06/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.06/2.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.06/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.06/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.06/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.06/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/2.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.06/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.06/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.06/2.05  
% 5.44/2.07  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.44/2.07  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.44/2.07  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.44/2.07  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.44/2.07  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.44/2.07  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.44/2.07  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.44/2.07  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 5.44/2.07  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.44/2.07  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.44/2.07  tff(f_58, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 5.44/2.07  tff(f_116, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.44/2.07  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.44/2.07  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.44/2.07  tff(f_76, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 5.44/2.07  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.44/2.07  tff(c_165, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.44/2.07  tff(c_178, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_165])).
% 5.44/2.07  tff(c_34, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, A_17), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.44/2.07  tff(c_42, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.44/2.07  tff(c_186, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_178, c_42])).
% 5.44/2.07  tff(c_198, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_186])).
% 5.44/2.07  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.44/2.07  tff(c_1889, plain, (![B_238, A_239]: (k1_tarski(k1_funct_1(B_238, A_239))=k2_relat_1(B_238) | k1_tarski(A_239)!=k1_relat_1(B_238) | ~v1_funct_1(B_238) | ~v1_relat_1(B_238))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.44/2.07  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.44/2.07  tff(c_1916, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1889, c_56])).
% 5.44/2.07  tff(c_1922, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_64, c_1916])).
% 5.44/2.07  tff(c_1951, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1922])).
% 5.44/2.07  tff(c_245, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.44/2.07  tff(c_258, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_245])).
% 5.44/2.07  tff(c_38, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.44/2.07  tff(c_269, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_258, c_38])).
% 5.44/2.07  tff(c_272, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_269])).
% 5.44/2.07  tff(c_44, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.44/2.07  tff(c_318, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_272, c_44])).
% 5.44/2.07  tff(c_322, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_318])).
% 5.44/2.07  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.44/2.07  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.44/2.07  tff(c_1989, plain, (![A_260, B_261, C_262, D_263]: (k1_enumset1(A_260, B_261, C_262)=D_263 | k2_tarski(A_260, C_262)=D_263 | k2_tarski(B_261, C_262)=D_263 | k2_tarski(A_260, B_261)=D_263 | k1_tarski(C_262)=D_263 | k1_tarski(B_261)=D_263 | k1_tarski(A_260)=D_263 | k1_xboole_0=D_263 | ~r1_tarski(D_263, k1_enumset1(A_260, B_261, C_262)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.44/2.07  tff(c_2008, plain, (![A_2, B_3, D_263]: (k1_enumset1(A_2, A_2, B_3)=D_263 | k2_tarski(A_2, B_3)=D_263 | k2_tarski(A_2, B_3)=D_263 | k2_tarski(A_2, A_2)=D_263 | k1_tarski(B_3)=D_263 | k1_tarski(A_2)=D_263 | k1_tarski(A_2)=D_263 | k1_xboole_0=D_263 | ~r1_tarski(D_263, k2_tarski(A_2, B_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1989])).
% 5.44/2.07  tff(c_2104, plain, (![A_290, B_291, D_292]: (k2_tarski(A_290, B_291)=D_292 | k2_tarski(A_290, B_291)=D_292 | k2_tarski(A_290, B_291)=D_292 | k1_tarski(A_290)=D_292 | k1_tarski(B_291)=D_292 | k1_tarski(A_290)=D_292 | k1_tarski(A_290)=D_292 | k1_xboole_0=D_292 | ~r1_tarski(D_292, k2_tarski(A_290, B_291)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_2008])).
% 5.44/2.07  tff(c_2130, plain, (![A_1, D_292]: (k2_tarski(A_1, A_1)=D_292 | k2_tarski(A_1, A_1)=D_292 | k2_tarski(A_1, A_1)=D_292 | k1_tarski(A_1)=D_292 | k1_tarski(A_1)=D_292 | k1_tarski(A_1)=D_292 | k1_tarski(A_1)=D_292 | k1_xboole_0=D_292 | ~r1_tarski(D_292, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2104])).
% 5.44/2.07  tff(c_2381, plain, (![A_333, D_334]: (k1_tarski(A_333)=D_334 | k1_tarski(A_333)=D_334 | k1_tarski(A_333)=D_334 | k1_tarski(A_333)=D_334 | k1_tarski(A_333)=D_334 | k1_tarski(A_333)=D_334 | k1_tarski(A_333)=D_334 | k1_xboole_0=D_334 | ~r1_tarski(D_334, k1_tarski(A_333)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_2, c_2130])).
% 5.44/2.07  tff(c_2394, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_322, c_2381])).
% 5.44/2.07  tff(c_2411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_1951, c_1951, c_1951, c_1951, c_1951, c_1951, c_1951, c_2394])).
% 5.44/2.07  tff(c_2413, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1922])).
% 5.44/2.07  tff(c_2420, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2413, c_60])).
% 5.44/2.07  tff(c_54, plain, (![A_33, B_34, C_35, D_36]: (k7_relset_1(A_33, B_34, C_35, D_36)=k9_relat_1(C_35, D_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.44/2.07  tff(c_2491, plain, (![D_36]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_36)=k9_relat_1('#skF_4', D_36))), inference(resolution, [status(thm)], [c_2420, c_54])).
% 5.44/2.07  tff(c_2412, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1922])).
% 5.44/2.07  tff(c_2630, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2413, c_2412])).
% 5.44/2.07  tff(c_2632, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2491, c_2630])).
% 5.44/2.07  tff(c_2650, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_2632])).
% 5.44/2.07  tff(c_2654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_2650])).
% 5.44/2.07  tff(c_2655, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_186])).
% 5.44/2.07  tff(c_26, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.44/2.07  tff(c_86, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.44/2.07  tff(c_98, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_26, c_86])).
% 5.44/2.07  tff(c_2659, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_2655, c_98])).
% 5.44/2.07  tff(c_36, plain, (![A_19]: (k9_relat_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.44/2.07  tff(c_2661, plain, (![A_19]: (k9_relat_1('#skF_4', A_19)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2655, c_2655, c_36])).
% 5.44/2.07  tff(c_2662, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_2655, c_26])).
% 5.44/2.07  tff(c_2900, plain, (![A_409, B_410, C_411, D_412]: (k7_relset_1(A_409, B_410, C_411, D_412)=k9_relat_1(C_411, D_412) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.44/2.07  tff(c_2903, plain, (![A_409, B_410, D_412]: (k7_relset_1(A_409, B_410, '#skF_4', D_412)=k9_relat_1('#skF_4', D_412))), inference(resolution, [status(thm)], [c_2662, c_2900])).
% 5.44/2.07  tff(c_2908, plain, (![A_409, B_410, D_412]: (k7_relset_1(A_409, B_410, '#skF_4', D_412)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_2903])).
% 5.44/2.07  tff(c_2910, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2908, c_56])).
% 5.44/2.07  tff(c_2913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2659, c_2910])).
% 5.44/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.07  
% 5.44/2.07  Inference rules
% 5.44/2.07  ----------------------
% 5.44/2.07  #Ref     : 0
% 5.44/2.07  #Sup     : 525
% 5.44/2.07  #Fact    : 20
% 5.44/2.07  #Define  : 0
% 5.44/2.07  #Split   : 8
% 5.44/2.07  #Chain   : 0
% 5.44/2.07  #Close   : 0
% 5.44/2.07  
% 5.44/2.07  Ordering : KBO
% 5.44/2.07  
% 5.44/2.07  Simplification rules
% 5.44/2.07  ----------------------
% 5.44/2.07  #Subsume      : 36
% 5.44/2.07  #Demod        : 661
% 5.44/2.07  #Tautology    : 272
% 5.44/2.07  #SimpNegUnit  : 39
% 5.44/2.07  #BackRed      : 102
% 5.44/2.07  
% 5.44/2.07  #Partial instantiations: 0
% 5.44/2.07  #Strategies tried      : 1
% 5.44/2.07  
% 5.44/2.07  Timing (in seconds)
% 5.44/2.07  ----------------------
% 5.44/2.07  Preprocessing        : 0.36
% 5.44/2.07  Parsing              : 0.19
% 5.44/2.07  CNF conversion       : 0.02
% 5.44/2.07  Main loop            : 0.85
% 5.44/2.07  Inferencing          : 0.30
% 5.44/2.07  Reduction            : 0.30
% 5.44/2.07  Demodulation         : 0.21
% 5.44/2.07  BG Simplification    : 0.04
% 5.44/2.07  Subsumption          : 0.14
% 5.44/2.07  Abstraction          : 0.06
% 5.44/2.07  MUC search           : 0.00
% 5.44/2.07  Cooper               : 0.00
% 5.44/2.07  Total                : 1.25
% 5.44/2.07  Index Insertion      : 0.00
% 5.44/2.07  Index Deletion       : 0.00
% 5.44/2.07  Index Matching       : 0.00
% 5.44/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
