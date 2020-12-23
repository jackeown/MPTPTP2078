%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:46 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 282 expanded)
%              Number of leaves         :   42 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 605 expanded)
%              Number of equality atoms :   47 ( 181 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_153,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_170,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_153])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k9_relat_1(B_23,A_22),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2264,plain,(
    ! [B_282,A_283] :
      ( k1_tarski(k1_funct_1(B_282,A_283)) = k2_relat_1(B_282)
      | k1_tarski(A_283) != k1_relat_1(B_282)
      | ~ v1_funct_1(B_282)
      | ~ v1_relat_1(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2215,plain,(
    ! [A_271,B_272,C_273,D_274] :
      ( k7_relset_1(A_271,B_272,C_273,D_274) = k9_relat_1(C_273,D_274)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2232,plain,(
    ! [D_274] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_274) = k9_relat_1('#skF_4',D_274) ),
    inference(resolution,[status(thm)],[c_66,c_2215])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2248,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2232,c_62])).

tff(c_2273,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2264,c_2248])).

tff(c_2285,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_70,c_2273])).

tff(c_2287,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2285])).

tff(c_402,plain,(
    ! [C_100,A_101,B_102] :
      ( v4_relat_1(C_100,A_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_421,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_402])).

tff(c_40,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2314,plain,(
    ! [B_285,C_286,A_287] :
      ( k2_tarski(B_285,C_286) = A_287
      | k1_tarski(C_286) = A_287
      | k1_tarski(B_285) = A_287
      | k1_xboole_0 = A_287
      | ~ r1_tarski(A_287,k2_tarski(B_285,C_286)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2331,plain,(
    ! [A_3,A_287] :
      ( k2_tarski(A_3,A_3) = A_287
      | k1_tarski(A_3) = A_287
      | k1_tarski(A_3) = A_287
      | k1_xboole_0 = A_287
      | ~ r1_tarski(A_287,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2314])).

tff(c_3340,plain,(
    ! [A_382,A_383] :
      ( k1_tarski(A_382) = A_383
      | k1_tarski(A_382) = A_383
      | k1_tarski(A_382) = A_383
      | k1_xboole_0 = A_383
      | ~ r1_tarski(A_383,k1_tarski(A_382)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2331])).

tff(c_3361,plain,(
    ! [A_384,B_385] :
      ( k1_tarski(A_384) = k1_relat_1(B_385)
      | k1_relat_1(B_385) = k1_xboole_0
      | ~ v4_relat_1(B_385,k1_tarski(A_384))
      | ~ v1_relat_1(B_385) ) ),
    inference(resolution,[status(thm)],[c_40,c_3340])).

tff(c_3403,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_421,c_3361])).

tff(c_3427,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_3403])).

tff(c_3428,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2287,c_3427])).

tff(c_2154,plain,(
    ! [A_263] :
      ( m1_subset_1(A_263,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_263),k2_relat_1(A_263))))
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2176,plain,(
    ! [A_263] :
      ( r1_tarski(A_263,k2_zfmisc_1(k1_relat_1(A_263),k2_relat_1(A_263)))
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(resolution,[status(thm)],[c_2154,c_32])).

tff(c_3484,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3428,c_2176])).

tff(c_3541,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_70,c_28,c_3484])).

tff(c_30,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_128,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_140,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_30,c_128])).

tff(c_231,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_140,c_231])).

tff(c_3589,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3541,c_246])).

tff(c_3638,plain,(
    ! [A_14] : r1_tarski('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3589,c_140])).

tff(c_44,plain,(
    ! [A_24] : k9_relat_1(k1_xboole_0,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3639,plain,(
    ! [A_24] : k9_relat_1('#skF_4',A_24) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3589,c_3589,c_44])).

tff(c_3779,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3639,c_2248])).

tff(c_3783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3638,c_3779])).

tff(c_3784,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2285])).

tff(c_3885,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_3784])).

tff(c_3889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_3885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:44:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.10  
% 5.17/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.10  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.17/2.10  
% 5.17/2.10  %Foreground sorts:
% 5.17/2.10  
% 5.17/2.10  
% 5.17/2.10  %Background operators:
% 5.17/2.10  
% 5.17/2.10  
% 5.17/2.10  %Foreground operators:
% 5.17/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.17/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.17/2.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.17/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.17/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/2.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.17/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.17/2.10  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.17/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.17/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.17/2.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.17/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.17/2.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.17/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.17/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.17/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.17/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.17/2.10  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.17/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.17/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.17/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.17/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.17/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.17/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.17/2.10  
% 5.28/2.12  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.28/2.12  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.28/2.12  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.28/2.12  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.28/2.12  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.28/2.12  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.28/2.12  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.28/2.12  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.28/2.12  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.28/2.12  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.28/2.12  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.28/2.12  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.28/2.12  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.28/2.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.28/2.12  tff(f_82, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 5.28/2.12  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.28/2.12  tff(c_153, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.28/2.12  tff(c_170, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_153])).
% 5.28/2.12  tff(c_42, plain, (![B_23, A_22]: (r1_tarski(k9_relat_1(B_23, A_22), k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.28/2.12  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.28/2.12  tff(c_28, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.28/2.12  tff(c_2264, plain, (![B_282, A_283]: (k1_tarski(k1_funct_1(B_282, A_283))=k2_relat_1(B_282) | k1_tarski(A_283)!=k1_relat_1(B_282) | ~v1_funct_1(B_282) | ~v1_relat_1(B_282))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.28/2.12  tff(c_2215, plain, (![A_271, B_272, C_273, D_274]: (k7_relset_1(A_271, B_272, C_273, D_274)=k9_relat_1(C_273, D_274) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.28/2.12  tff(c_2232, plain, (![D_274]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_274)=k9_relat_1('#skF_4', D_274))), inference(resolution, [status(thm)], [c_66, c_2215])).
% 5.28/2.12  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.28/2.12  tff(c_2248, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2232, c_62])).
% 5.28/2.12  tff(c_2273, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2264, c_2248])).
% 5.28/2.12  tff(c_2285, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_70, c_2273])).
% 5.28/2.12  tff(c_2287, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2285])).
% 5.28/2.12  tff(c_402, plain, (![C_100, A_101, B_102]: (v4_relat_1(C_100, A_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.28/2.12  tff(c_421, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_402])).
% 5.28/2.12  tff(c_40, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(B_21), A_20) | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.28/2.12  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.28/2.12  tff(c_2314, plain, (![B_285, C_286, A_287]: (k2_tarski(B_285, C_286)=A_287 | k1_tarski(C_286)=A_287 | k1_tarski(B_285)=A_287 | k1_xboole_0=A_287 | ~r1_tarski(A_287, k2_tarski(B_285, C_286)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.28/2.12  tff(c_2331, plain, (![A_3, A_287]: (k2_tarski(A_3, A_3)=A_287 | k1_tarski(A_3)=A_287 | k1_tarski(A_3)=A_287 | k1_xboole_0=A_287 | ~r1_tarski(A_287, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2314])).
% 5.28/2.12  tff(c_3340, plain, (![A_382, A_383]: (k1_tarski(A_382)=A_383 | k1_tarski(A_382)=A_383 | k1_tarski(A_382)=A_383 | k1_xboole_0=A_383 | ~r1_tarski(A_383, k1_tarski(A_382)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2331])).
% 5.28/2.12  tff(c_3361, plain, (![A_384, B_385]: (k1_tarski(A_384)=k1_relat_1(B_385) | k1_relat_1(B_385)=k1_xboole_0 | ~v4_relat_1(B_385, k1_tarski(A_384)) | ~v1_relat_1(B_385))), inference(resolution, [status(thm)], [c_40, c_3340])).
% 5.28/2.12  tff(c_3403, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_421, c_3361])).
% 5.28/2.12  tff(c_3427, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_170, c_3403])).
% 5.28/2.12  tff(c_3428, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2287, c_3427])).
% 5.28/2.12  tff(c_2154, plain, (![A_263]: (m1_subset_1(A_263, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_263), k2_relat_1(A_263)))) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.28/2.12  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.28/2.12  tff(c_2176, plain, (![A_263]: (r1_tarski(A_263, k2_zfmisc_1(k1_relat_1(A_263), k2_relat_1(A_263))) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(resolution, [status(thm)], [c_2154, c_32])).
% 5.28/2.12  tff(c_3484, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3428, c_2176])).
% 5.28/2.12  tff(c_3541, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_170, c_70, c_28, c_3484])).
% 5.28/2.12  tff(c_30, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.28/2.12  tff(c_128, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.28/2.12  tff(c_140, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_30, c_128])).
% 5.28/2.12  tff(c_231, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.28/2.12  tff(c_246, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_140, c_231])).
% 5.28/2.12  tff(c_3589, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3541, c_246])).
% 5.28/2.12  tff(c_3638, plain, (![A_14]: (r1_tarski('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_3589, c_140])).
% 5.28/2.12  tff(c_44, plain, (![A_24]: (k9_relat_1(k1_xboole_0, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.28/2.12  tff(c_3639, plain, (![A_24]: (k9_relat_1('#skF_4', A_24)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3589, c_3589, c_44])).
% 5.28/2.12  tff(c_3779, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3639, c_2248])).
% 5.28/2.12  tff(c_3783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3638, c_3779])).
% 5.28/2.12  tff(c_3784, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2285])).
% 5.28/2.12  tff(c_3885, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_3784])).
% 5.28/2.12  tff(c_3889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_3885])).
% 5.28/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.12  
% 5.28/2.12  Inference rules
% 5.28/2.12  ----------------------
% 5.28/2.12  #Ref     : 0
% 5.28/2.12  #Sup     : 795
% 5.28/2.12  #Fact    : 0
% 5.28/2.12  #Define  : 0
% 5.28/2.12  #Split   : 4
% 5.28/2.12  #Chain   : 0
% 5.28/2.12  #Close   : 0
% 5.28/2.12  
% 5.28/2.12  Ordering : KBO
% 5.28/2.12  
% 5.28/2.12  Simplification rules
% 5.28/2.12  ----------------------
% 5.28/2.12  #Subsume      : 79
% 5.28/2.12  #Demod        : 1335
% 5.28/2.12  #Tautology    : 464
% 5.28/2.12  #SimpNegUnit  : 2
% 5.28/2.12  #BackRed      : 116
% 5.28/2.12  
% 5.28/2.12  #Partial instantiations: 0
% 5.28/2.12  #Strategies tried      : 1
% 5.28/2.12  
% 5.28/2.12  Timing (in seconds)
% 5.28/2.12  ----------------------
% 5.28/2.12  Preprocessing        : 0.42
% 5.28/2.12  Parsing              : 0.24
% 5.28/2.12  CNF conversion       : 0.02
% 5.28/2.12  Main loop            : 0.85
% 5.28/2.12  Inferencing          : 0.28
% 5.28/2.12  Reduction            : 0.32
% 5.28/2.12  Demodulation         : 0.24
% 5.28/2.12  BG Simplification    : 0.03
% 5.28/2.12  Subsumption          : 0.15
% 5.28/2.12  Abstraction          : 0.04
% 5.28/2.12  MUC search           : 0.00
% 5.28/2.12  Cooper               : 0.00
% 5.28/2.12  Total                : 1.30
% 5.28/2.12  Index Insertion      : 0.00
% 5.28/2.12  Index Deletion       : 0.00
% 5.28/2.12  Index Matching       : 0.00
% 5.28/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
