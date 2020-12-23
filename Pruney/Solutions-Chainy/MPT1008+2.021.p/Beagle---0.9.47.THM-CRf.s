%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:28 EST 2020

% Result     : Theorem 16.74s
% Output     : CNFRefutation 16.93s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 632 expanded)
%              Number of leaves         :   47 ( 225 expanded)
%              Depth                    :   14
%              Number of atoms          :  282 (1393 expanded)
%              Number of equality atoms :  152 ( 610 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_136,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_248,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_261,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_248])).

tff(c_52,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_271,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_261,c_52])).

tff(c_273,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_88,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1030,plain,(
    ! [B_193,A_194] :
      ( k1_tarski(k1_funct_1(B_193,A_194)) = k2_relat_1(B_193)
      | k1_tarski(A_194) != k1_relat_1(B_193)
      | ~ v1_funct_1(B_193)
      | ~ v1_relat_1(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_638,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_651,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_638])).

tff(c_80,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_661,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_80])).

tff(c_1036,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_661])).

tff(c_1061,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_88,c_1036])).

tff(c_530,plain,(
    ! [C_126,A_127,B_128] :
      ( v4_relat_1(C_126,A_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_543,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_530])).

tff(c_44,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1351,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( k1_enumset1(A_220,B_221,C_222) = D_223
      | k2_tarski(A_220,C_222) = D_223
      | k2_tarski(B_221,C_222) = D_223
      | k2_tarski(A_220,B_221) = D_223
      | k1_tarski(C_222) = D_223
      | k1_tarski(B_221) = D_223
      | k1_tarski(A_220) = D_223
      | k1_xboole_0 = D_223
      | ~ r1_tarski(D_223,k1_enumset1(A_220,B_221,C_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1378,plain,(
    ! [A_4,B_5,D_223] :
      ( k1_enumset1(A_4,A_4,B_5) = D_223
      | k2_tarski(A_4,B_5) = D_223
      | k2_tarski(A_4,B_5) = D_223
      | k2_tarski(A_4,A_4) = D_223
      | k1_tarski(B_5) = D_223
      | k1_tarski(A_4) = D_223
      | k1_tarski(A_4) = D_223
      | k1_xboole_0 = D_223
      | ~ r1_tarski(D_223,k2_tarski(A_4,B_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1351])).

tff(c_8556,plain,(
    ! [A_667,B_668,D_669] :
      ( k2_tarski(A_667,B_668) = D_669
      | k2_tarski(A_667,B_668) = D_669
      | k2_tarski(A_667,B_668) = D_669
      | k1_tarski(A_667) = D_669
      | k1_tarski(B_668) = D_669
      | k1_tarski(A_667) = D_669
      | k1_tarski(A_667) = D_669
      | k1_xboole_0 = D_669
      | ~ r1_tarski(D_669,k2_tarski(A_667,B_668)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_1378])).

tff(c_8589,plain,(
    ! [A_3,D_669] :
      ( k2_tarski(A_3,A_3) = D_669
      | k2_tarski(A_3,A_3) = D_669
      | k2_tarski(A_3,A_3) = D_669
      | k1_tarski(A_3) = D_669
      | k1_tarski(A_3) = D_669
      | k1_tarski(A_3) = D_669
      | k1_tarski(A_3) = D_669
      | k1_xboole_0 = D_669
      | ~ r1_tarski(D_669,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_8556])).

tff(c_34226,plain,(
    ! [A_1197,D_1198] :
      ( k1_tarski(A_1197) = D_1198
      | k1_tarski(A_1197) = D_1198
      | k1_tarski(A_1197) = D_1198
      | k1_tarski(A_1197) = D_1198
      | k1_tarski(A_1197) = D_1198
      | k1_tarski(A_1197) = D_1198
      | k1_tarski(A_1197) = D_1198
      | k1_xboole_0 = D_1198
      | ~ r1_tarski(D_1198,k1_tarski(A_1197)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_8589])).

tff(c_34590,plain,(
    ! [A_1204,B_1205] :
      ( k1_tarski(A_1204) = k1_relat_1(B_1205)
      | k1_relat_1(B_1205) = k1_xboole_0
      | ~ v4_relat_1(B_1205,k1_tarski(A_1204))
      | ~ v1_relat_1(B_1205) ) ),
    inference(resolution,[status(thm)],[c_44,c_34226])).

tff(c_34712,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_543,c_34590])).

tff(c_34770,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_34712])).

tff(c_34772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_1061,c_34770])).

tff(c_34773,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34784,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34773,c_34773,c_46])).

tff(c_50,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_270,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_261,c_50])).

tff(c_272,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_34775,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34773,c_272])).

tff(c_34820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34784,c_34775])).

tff(c_34821,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_34,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_128,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | ~ m1_subset_1(A_65,k1_zfmisc_1(B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_34876,plain,(
    ! [A_13] : r1_tarski('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_132])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34833,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_34821,c_48])).

tff(c_34823,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_34867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34833,c_34821,c_34823])).

tff(c_34869,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_34893,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_34869])).

tff(c_35061,plain,(
    ! [B_1234,A_1235] :
      ( v4_relat_1(B_1234,A_1235)
      | ~ r1_tarski(k1_relat_1(B_1234),A_1235)
      | ~ v1_relat_1(B_1234) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_35064,plain,(
    ! [A_1235] :
      ( v4_relat_1('#skF_4',A_1235)
      | ~ r1_tarski('#skF_4',A_1235)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34893,c_35061])).

tff(c_35073,plain,(
    ! [A_1235] : v4_relat_1('#skF_4',A_1235) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_34876,c_35064])).

tff(c_70,plain,(
    ! [A_41] : k1_relat_1('#skF_1'(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_74,plain,(
    ! [A_41] : v1_relat_1('#skF_1'(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_135,plain,(
    ! [A_68] :
      ( k1_relat_1(A_68) != k1_xboole_0
      | k1_xboole_0 = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_138,plain,(
    ! [A_41] :
      ( k1_relat_1('#skF_1'(A_41)) != k1_xboole_0
      | '#skF_1'(A_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_135])).

tff(c_140,plain,(
    ! [A_41] :
      ( k1_xboole_0 != A_41
      | '#skF_1'(A_41) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_138])).

tff(c_34874,plain,(
    ! [A_41] :
      ( A_41 != '#skF_4'
      | '#skF_1'(A_41) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_34821,c_140])).

tff(c_35123,plain,(
    ! [B_1247,A_1248] :
      ( r1_tarski(k1_relat_1(B_1247),A_1248)
      | ~ v4_relat_1(B_1247,A_1248)
      | ~ v1_relat_1(B_1247) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_35142,plain,(
    ! [A_41,A_1248] :
      ( r1_tarski(A_41,A_1248)
      | ~ v4_relat_1('#skF_1'(A_41),A_1248)
      | ~ v1_relat_1('#skF_1'(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_35123])).

tff(c_35151,plain,(
    ! [A_1249,A_1250] :
      ( r1_tarski(A_1249,A_1250)
      | ~ v4_relat_1('#skF_1'(A_1249),A_1250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_35142])).

tff(c_35164,plain,(
    ! [A_41,A_1250] :
      ( r1_tarski(A_41,A_1250)
      | ~ v4_relat_1('#skF_4',A_1250)
      | A_41 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34874,c_35151])).

tff(c_35175,plain,(
    ! [A_1251,A_1252] :
      ( r1_tarski(A_1251,A_1252)
      | A_1251 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35073,c_35164])).

tff(c_38,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_260,plain,(
    ! [A_14,A_87,B_88] :
      ( v1_relat_1(A_14)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_38,c_248])).

tff(c_35198,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_35175,c_260])).

tff(c_35194,plain,(
    ! [A_1251] :
      ( v1_relat_1(A_1251)
      | A_1251 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_35175,c_260])).

tff(c_35172,plain,(
    ! [A_41,A_1250] :
      ( r1_tarski(A_41,A_1250)
      | A_41 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35073,c_35164])).

tff(c_35287,plain,(
    ! [C_1266,A_1267,B_1268] :
      ( v4_relat_1(C_1266,A_1267)
      | ~ m1_subset_1(C_1266,k1_zfmisc_1(k2_zfmisc_1(A_1267,B_1268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_35302,plain,(
    ! [A_1271,A_1272,B_1273] :
      ( v4_relat_1(A_1271,A_1272)
      | ~ r1_tarski(A_1271,k2_zfmisc_1(A_1272,B_1273)) ) ),
    inference(resolution,[status(thm)],[c_38,c_35287])).

tff(c_35315,plain,(
    ! [A_41,A_1272] :
      ( v4_relat_1(A_41,A_1272)
      | A_41 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_35172,c_35302])).

tff(c_34933,plain,(
    ! [A_1216] : r1_tarski('#skF_4',A_1216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_132])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34936,plain,(
    ! [A_1216] :
      ( A_1216 = '#skF_4'
      | ~ r1_tarski(A_1216,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34933,c_4])).

tff(c_35411,plain,(
    ! [B_1295] :
      ( k1_relat_1(B_1295) = '#skF_4'
      | ~ v4_relat_1(B_1295,'#skF_4')
      | ~ v1_relat_1(B_1295) ) ),
    inference(resolution,[status(thm)],[c_35123,c_34936])).

tff(c_35503,plain,(
    ! [A_1308] :
      ( k1_relat_1(A_1308) = '#skF_4'
      | ~ v1_relat_1(A_1308)
      | A_1308 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_35315,c_35411])).

tff(c_35521,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35194,c_35503])).

tff(c_34822,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_34898,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_34822])).

tff(c_35580,plain,(
    ! [B_1315,A_1316] :
      ( k1_tarski(k1_funct_1(B_1315,A_1316)) = k2_relat_1(B_1315)
      | k1_tarski(A_1316) != k1_relat_1(B_1315)
      | ~ v1_funct_1(B_1315)
      | ~ v1_relat_1(B_1315) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34877,plain,(
    ! [A_13] : m1_subset_1('#skF_4',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_34])).

tff(c_35443,plain,(
    ! [A_1296,B_1297,C_1298] :
      ( k2_relset_1(A_1296,B_1297,C_1298) = k2_relat_1(C_1298)
      | ~ m1_subset_1(C_1298,k1_zfmisc_1(k2_zfmisc_1(A_1296,B_1297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_35447,plain,(
    ! [A_1296,B_1297] : k2_relset_1(A_1296,B_1297,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34877,c_35443])).

tff(c_35453,plain,(
    ! [A_1296,B_1297] : k2_relset_1(A_1296,B_1297,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34898,c_35447])).

tff(c_35455,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35453,c_80])).

tff(c_35586,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_35580,c_35455])).

tff(c_35610,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35198,c_88,c_35521,c_34898,c_35586])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_34881,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_82])).

tff(c_86,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_35485,plain,(
    ! [A_1302,B_1303,C_1304,D_1305] :
      ( k8_relset_1(A_1302,B_1303,C_1304,D_1305) = k10_relat_1(C_1304,D_1305)
      | ~ m1_subset_1(C_1304,k1_zfmisc_1(k2_zfmisc_1(A_1302,B_1303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_35492,plain,(
    ! [A_1302,B_1303,D_1305] : k8_relset_1(A_1302,B_1303,'#skF_4',D_1305) = k10_relat_1('#skF_4',D_1305) ),
    inference(resolution,[status(thm)],[c_34877,c_35485])).

tff(c_35664,plain,(
    ! [A_1319,B_1320,C_1321,D_1322] :
      ( m1_subset_1(k8_relset_1(A_1319,B_1320,C_1321,D_1322),k1_zfmisc_1(A_1319))
      | ~ m1_subset_1(C_1321,k1_zfmisc_1(k2_zfmisc_1(A_1319,B_1320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_35691,plain,(
    ! [D_1305,A_1302,B_1303] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_1305),k1_zfmisc_1(A_1302))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1302,B_1303))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35492,c_35664])).

tff(c_35701,plain,(
    ! [D_1323,A_1324] : m1_subset_1(k10_relat_1('#skF_4',D_1323),k1_zfmisc_1(A_1324)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34877,c_35691])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_35750,plain,(
    ! [D_1328,A_1329] : r1_tarski(k10_relat_1('#skF_4',D_1328),A_1329) ),
    inference(resolution,[status(thm)],[c_35701,c_36])).

tff(c_35782,plain,(
    ! [D_1328] : k10_relat_1('#skF_4',D_1328) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35750,c_34936])).

tff(c_35788,plain,(
    ! [A_1302,B_1303,D_1305] : k8_relset_1(A_1302,B_1303,'#skF_4',D_1305) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35782,c_35492])).

tff(c_78,plain,(
    ! [B_48,A_47,C_49] :
      ( k1_xboole_0 = B_48
      | k8_relset_1(A_47,B_48,C_49,B_48) = A_47
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_2(C_49,A_47,B_48)
      | ~ v1_funct_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_35820,plain,(
    ! [B_1333,A_1334,C_1335] :
      ( B_1333 = '#skF_4'
      | k8_relset_1(A_1334,B_1333,C_1335,B_1333) = A_1334
      | ~ m1_subset_1(C_1335,k1_zfmisc_1(k2_zfmisc_1(A_1334,B_1333)))
      | ~ v1_funct_2(C_1335,A_1334,B_1333)
      | ~ v1_funct_1(C_1335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34821,c_78])).

tff(c_35826,plain,(
    ! [B_1333,A_1334] :
      ( B_1333 = '#skF_4'
      | k8_relset_1(A_1334,B_1333,'#skF_4',B_1333) = A_1334
      | ~ v1_funct_2('#skF_4',A_1334,B_1333)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34877,c_35820])).

tff(c_35833,plain,(
    ! [B_1333,A_1334] :
      ( B_1333 = '#skF_4'
      | k8_relset_1(A_1334,B_1333,'#skF_4',B_1333) = A_1334
      | ~ v1_funct_2('#skF_4',A_1334,B_1333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_35826])).

tff(c_43193,plain,(
    ! [B_1823,A_1824] :
      ( B_1823 = '#skF_4'
      | A_1824 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_1824,B_1823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35788,c_35833])).

tff(c_43196,plain,
    ( '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_86,c_43193])).

tff(c_43200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35610,c_34881,c_43196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.74/8.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.74/8.23  
% 16.74/8.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.74/8.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 16.74/8.24  
% 16.74/8.24  %Foreground sorts:
% 16.74/8.24  
% 16.74/8.24  
% 16.74/8.24  %Background operators:
% 16.74/8.24  
% 16.74/8.24  
% 16.74/8.24  %Foreground operators:
% 16.74/8.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 16.74/8.24  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 16.74/8.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.74/8.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.74/8.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.74/8.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.74/8.24  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 16.74/8.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.74/8.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.74/8.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.74/8.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.74/8.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.74/8.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.74/8.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.74/8.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.74/8.24  tff('#skF_2', type, '#skF_2': $i).
% 16.74/8.24  tff('#skF_3', type, '#skF_3': $i).
% 16.74/8.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.74/8.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.74/8.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 16.74/8.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.74/8.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 16.74/8.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.74/8.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.74/8.24  tff('#skF_4', type, '#skF_4': $i).
% 16.74/8.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.74/8.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.74/8.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.74/8.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.74/8.24  
% 16.93/8.26  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 16.93/8.26  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.93/8.26  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 16.93/8.26  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 16.93/8.26  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 16.93/8.26  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.93/8.26  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 16.93/8.26  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 16.93/8.26  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 16.93/8.26  tff(f_65, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 16.93/8.26  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 16.93/8.26  tff(f_67, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 16.93/8.26  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.93/8.26  tff(f_136, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_tarski(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e15_31__wellord2)).
% 16.93/8.26  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.93/8.26  tff(f_124, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 16.93/8.26  tff(f_116, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 16.93/8.26  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 16.93/8.26  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 16.93/8.26  tff(c_248, plain, (![C_86, A_87, B_88]: (v1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.93/8.26  tff(c_261, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_248])).
% 16.93/8.26  tff(c_52, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.93/8.26  tff(c_271, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_261, c_52])).
% 16.93/8.26  tff(c_273, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_271])).
% 16.93/8.26  tff(c_88, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 16.93/8.26  tff(c_1030, plain, (![B_193, A_194]: (k1_tarski(k1_funct_1(B_193, A_194))=k2_relat_1(B_193) | k1_tarski(A_194)!=k1_relat_1(B_193) | ~v1_funct_1(B_193) | ~v1_relat_1(B_193))), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.93/8.26  tff(c_638, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 16.93/8.26  tff(c_651, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_638])).
% 16.93/8.26  tff(c_80, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 16.93/8.26  tff(c_661, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_651, c_80])).
% 16.93/8.26  tff(c_1036, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1030, c_661])).
% 16.93/8.26  tff(c_1061, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_88, c_1036])).
% 16.93/8.26  tff(c_530, plain, (![C_126, A_127, B_128]: (v4_relat_1(C_126, A_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 16.93/8.26  tff(c_543, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_84, c_530])).
% 16.93/8.26  tff(c_44, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.93/8.26  tff(c_10, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.93/8.26  tff(c_12, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.93/8.26  tff(c_1351, plain, (![A_220, B_221, C_222, D_223]: (k1_enumset1(A_220, B_221, C_222)=D_223 | k2_tarski(A_220, C_222)=D_223 | k2_tarski(B_221, C_222)=D_223 | k2_tarski(A_220, B_221)=D_223 | k1_tarski(C_222)=D_223 | k1_tarski(B_221)=D_223 | k1_tarski(A_220)=D_223 | k1_xboole_0=D_223 | ~r1_tarski(D_223, k1_enumset1(A_220, B_221, C_222)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.93/8.26  tff(c_1378, plain, (![A_4, B_5, D_223]: (k1_enumset1(A_4, A_4, B_5)=D_223 | k2_tarski(A_4, B_5)=D_223 | k2_tarski(A_4, B_5)=D_223 | k2_tarski(A_4, A_4)=D_223 | k1_tarski(B_5)=D_223 | k1_tarski(A_4)=D_223 | k1_tarski(A_4)=D_223 | k1_xboole_0=D_223 | ~r1_tarski(D_223, k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1351])).
% 16.93/8.26  tff(c_8556, plain, (![A_667, B_668, D_669]: (k2_tarski(A_667, B_668)=D_669 | k2_tarski(A_667, B_668)=D_669 | k2_tarski(A_667, B_668)=D_669 | k1_tarski(A_667)=D_669 | k1_tarski(B_668)=D_669 | k1_tarski(A_667)=D_669 | k1_tarski(A_667)=D_669 | k1_xboole_0=D_669 | ~r1_tarski(D_669, k2_tarski(A_667, B_668)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_1378])).
% 16.93/8.26  tff(c_8589, plain, (![A_3, D_669]: (k2_tarski(A_3, A_3)=D_669 | k2_tarski(A_3, A_3)=D_669 | k2_tarski(A_3, A_3)=D_669 | k1_tarski(A_3)=D_669 | k1_tarski(A_3)=D_669 | k1_tarski(A_3)=D_669 | k1_tarski(A_3)=D_669 | k1_xboole_0=D_669 | ~r1_tarski(D_669, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_8556])).
% 16.93/8.26  tff(c_34226, plain, (![A_1197, D_1198]: (k1_tarski(A_1197)=D_1198 | k1_tarski(A_1197)=D_1198 | k1_tarski(A_1197)=D_1198 | k1_tarski(A_1197)=D_1198 | k1_tarski(A_1197)=D_1198 | k1_tarski(A_1197)=D_1198 | k1_tarski(A_1197)=D_1198 | k1_xboole_0=D_1198 | ~r1_tarski(D_1198, k1_tarski(A_1197)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_8589])).
% 16.93/8.26  tff(c_34590, plain, (![A_1204, B_1205]: (k1_tarski(A_1204)=k1_relat_1(B_1205) | k1_relat_1(B_1205)=k1_xboole_0 | ~v4_relat_1(B_1205, k1_tarski(A_1204)) | ~v1_relat_1(B_1205))), inference(resolution, [status(thm)], [c_44, c_34226])).
% 16.93/8.26  tff(c_34712, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_543, c_34590])).
% 16.93/8.26  tff(c_34770, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_261, c_34712])).
% 16.93/8.26  tff(c_34772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_1061, c_34770])).
% 16.93/8.26  tff(c_34773, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_271])).
% 16.93/8.26  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.93/8.26  tff(c_34784, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34773, c_34773, c_46])).
% 16.93/8.26  tff(c_50, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.93/8.26  tff(c_270, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_261, c_50])).
% 16.93/8.26  tff(c_272, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_270])).
% 16.93/8.26  tff(c_34775, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34773, c_272])).
% 16.93/8.26  tff(c_34820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34784, c_34775])).
% 16.93/8.26  tff(c_34821, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_270])).
% 16.93/8.26  tff(c_34, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.93/8.26  tff(c_128, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | ~m1_subset_1(A_65, k1_zfmisc_1(B_66)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.93/8.26  tff(c_132, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_34, c_128])).
% 16.93/8.26  tff(c_34876, plain, (![A_13]: (r1_tarski('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_132])).
% 16.93/8.26  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.93/8.26  tff(c_34833, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_34821, c_48])).
% 16.93/8.26  tff(c_34823, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_271])).
% 16.93/8.26  tff(c_34867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34833, c_34821, c_34823])).
% 16.93/8.26  tff(c_34869, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_271])).
% 16.93/8.26  tff(c_34893, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_34869])).
% 16.93/8.26  tff(c_35061, plain, (![B_1234, A_1235]: (v4_relat_1(B_1234, A_1235) | ~r1_tarski(k1_relat_1(B_1234), A_1235) | ~v1_relat_1(B_1234))), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.93/8.26  tff(c_35064, plain, (![A_1235]: (v4_relat_1('#skF_4', A_1235) | ~r1_tarski('#skF_4', A_1235) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34893, c_35061])).
% 16.93/8.26  tff(c_35073, plain, (![A_1235]: (v4_relat_1('#skF_4', A_1235))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_34876, c_35064])).
% 16.93/8.26  tff(c_70, plain, (![A_41]: (k1_relat_1('#skF_1'(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_136])).
% 16.93/8.26  tff(c_74, plain, (![A_41]: (v1_relat_1('#skF_1'(A_41)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 16.93/8.26  tff(c_135, plain, (![A_68]: (k1_relat_1(A_68)!=k1_xboole_0 | k1_xboole_0=A_68 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.93/8.26  tff(c_138, plain, (![A_41]: (k1_relat_1('#skF_1'(A_41))!=k1_xboole_0 | '#skF_1'(A_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_135])).
% 16.93/8.26  tff(c_140, plain, (![A_41]: (k1_xboole_0!=A_41 | '#skF_1'(A_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_138])).
% 16.93/8.26  tff(c_34874, plain, (![A_41]: (A_41!='#skF_4' | '#skF_1'(A_41)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_34821, c_140])).
% 16.93/8.26  tff(c_35123, plain, (![B_1247, A_1248]: (r1_tarski(k1_relat_1(B_1247), A_1248) | ~v4_relat_1(B_1247, A_1248) | ~v1_relat_1(B_1247))), inference(cnfTransformation, [status(thm)], [f_83])).
% 16.93/8.26  tff(c_35142, plain, (![A_41, A_1248]: (r1_tarski(A_41, A_1248) | ~v4_relat_1('#skF_1'(A_41), A_1248) | ~v1_relat_1('#skF_1'(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_35123])).
% 16.93/8.26  tff(c_35151, plain, (![A_1249, A_1250]: (r1_tarski(A_1249, A_1250) | ~v4_relat_1('#skF_1'(A_1249), A_1250))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_35142])).
% 16.93/8.26  tff(c_35164, plain, (![A_41, A_1250]: (r1_tarski(A_41, A_1250) | ~v4_relat_1('#skF_4', A_1250) | A_41!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34874, c_35151])).
% 16.93/8.26  tff(c_35175, plain, (![A_1251, A_1252]: (r1_tarski(A_1251, A_1252) | A_1251!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35073, c_35164])).
% 16.93/8.26  tff(c_38, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.93/8.26  tff(c_260, plain, (![A_14, A_87, B_88]: (v1_relat_1(A_14) | ~r1_tarski(A_14, k2_zfmisc_1(A_87, B_88)))), inference(resolution, [status(thm)], [c_38, c_248])).
% 16.93/8.26  tff(c_35198, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_35175, c_260])).
% 16.93/8.26  tff(c_35194, plain, (![A_1251]: (v1_relat_1(A_1251) | A_1251!='#skF_4')), inference(resolution, [status(thm)], [c_35175, c_260])).
% 16.93/8.26  tff(c_35172, plain, (![A_41, A_1250]: (r1_tarski(A_41, A_1250) | A_41!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35073, c_35164])).
% 16.93/8.26  tff(c_35287, plain, (![C_1266, A_1267, B_1268]: (v4_relat_1(C_1266, A_1267) | ~m1_subset_1(C_1266, k1_zfmisc_1(k2_zfmisc_1(A_1267, B_1268))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 16.93/8.26  tff(c_35302, plain, (![A_1271, A_1272, B_1273]: (v4_relat_1(A_1271, A_1272) | ~r1_tarski(A_1271, k2_zfmisc_1(A_1272, B_1273)))), inference(resolution, [status(thm)], [c_38, c_35287])).
% 16.93/8.26  tff(c_35315, plain, (![A_41, A_1272]: (v4_relat_1(A_41, A_1272) | A_41!='#skF_4')), inference(resolution, [status(thm)], [c_35172, c_35302])).
% 16.93/8.26  tff(c_34933, plain, (![A_1216]: (r1_tarski('#skF_4', A_1216))), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_132])).
% 16.93/8.26  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.93/8.26  tff(c_34936, plain, (![A_1216]: (A_1216='#skF_4' | ~r1_tarski(A_1216, '#skF_4'))), inference(resolution, [status(thm)], [c_34933, c_4])).
% 16.93/8.26  tff(c_35411, plain, (![B_1295]: (k1_relat_1(B_1295)='#skF_4' | ~v4_relat_1(B_1295, '#skF_4') | ~v1_relat_1(B_1295))), inference(resolution, [status(thm)], [c_35123, c_34936])).
% 16.93/8.26  tff(c_35503, plain, (![A_1308]: (k1_relat_1(A_1308)='#skF_4' | ~v1_relat_1(A_1308) | A_1308!='#skF_4')), inference(resolution, [status(thm)], [c_35315, c_35411])).
% 16.93/8.26  tff(c_35521, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_35194, c_35503])).
% 16.93/8.26  tff(c_34822, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_270])).
% 16.93/8.26  tff(c_34898, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_34822])).
% 16.93/8.26  tff(c_35580, plain, (![B_1315, A_1316]: (k1_tarski(k1_funct_1(B_1315, A_1316))=k2_relat_1(B_1315) | k1_tarski(A_1316)!=k1_relat_1(B_1315) | ~v1_funct_1(B_1315) | ~v1_relat_1(B_1315))), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.93/8.26  tff(c_34877, plain, (![A_13]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_34])).
% 16.93/8.26  tff(c_35443, plain, (![A_1296, B_1297, C_1298]: (k2_relset_1(A_1296, B_1297, C_1298)=k2_relat_1(C_1298) | ~m1_subset_1(C_1298, k1_zfmisc_1(k2_zfmisc_1(A_1296, B_1297))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 16.93/8.26  tff(c_35447, plain, (![A_1296, B_1297]: (k2_relset_1(A_1296, B_1297, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34877, c_35443])).
% 16.93/8.26  tff(c_35453, plain, (![A_1296, B_1297]: (k2_relset_1(A_1296, B_1297, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34898, c_35447])).
% 16.93/8.26  tff(c_35455, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35453, c_80])).
% 16.93/8.26  tff(c_35586, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35580, c_35455])).
% 16.93/8.26  tff(c_35610, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35198, c_88, c_35521, c_34898, c_35586])).
% 16.93/8.26  tff(c_82, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_160])).
% 16.93/8.26  tff(c_34881, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_82])).
% 16.93/8.26  tff(c_86, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 16.93/8.26  tff(c_35485, plain, (![A_1302, B_1303, C_1304, D_1305]: (k8_relset_1(A_1302, B_1303, C_1304, D_1305)=k10_relat_1(C_1304, D_1305) | ~m1_subset_1(C_1304, k1_zfmisc_1(k2_zfmisc_1(A_1302, B_1303))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.93/8.26  tff(c_35492, plain, (![A_1302, B_1303, D_1305]: (k8_relset_1(A_1302, B_1303, '#skF_4', D_1305)=k10_relat_1('#skF_4', D_1305))), inference(resolution, [status(thm)], [c_34877, c_35485])).
% 16.93/8.26  tff(c_35664, plain, (![A_1319, B_1320, C_1321, D_1322]: (m1_subset_1(k8_relset_1(A_1319, B_1320, C_1321, D_1322), k1_zfmisc_1(A_1319)) | ~m1_subset_1(C_1321, k1_zfmisc_1(k2_zfmisc_1(A_1319, B_1320))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.93/8.26  tff(c_35691, plain, (![D_1305, A_1302, B_1303]: (m1_subset_1(k10_relat_1('#skF_4', D_1305), k1_zfmisc_1(A_1302)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1302, B_1303))))), inference(superposition, [status(thm), theory('equality')], [c_35492, c_35664])).
% 16.93/8.26  tff(c_35701, plain, (![D_1323, A_1324]: (m1_subset_1(k10_relat_1('#skF_4', D_1323), k1_zfmisc_1(A_1324)))), inference(demodulation, [status(thm), theory('equality')], [c_34877, c_35691])).
% 16.93/8.26  tff(c_36, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.93/8.26  tff(c_35750, plain, (![D_1328, A_1329]: (r1_tarski(k10_relat_1('#skF_4', D_1328), A_1329))), inference(resolution, [status(thm)], [c_35701, c_36])).
% 16.93/8.26  tff(c_35782, plain, (![D_1328]: (k10_relat_1('#skF_4', D_1328)='#skF_4')), inference(resolution, [status(thm)], [c_35750, c_34936])).
% 16.93/8.26  tff(c_35788, plain, (![A_1302, B_1303, D_1305]: (k8_relset_1(A_1302, B_1303, '#skF_4', D_1305)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35782, c_35492])).
% 16.93/8.26  tff(c_78, plain, (![B_48, A_47, C_49]: (k1_xboole_0=B_48 | k8_relset_1(A_47, B_48, C_49, B_48)=A_47 | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_2(C_49, A_47, B_48) | ~v1_funct_1(C_49))), inference(cnfTransformation, [status(thm)], [f_148])).
% 16.93/8.26  tff(c_35820, plain, (![B_1333, A_1334, C_1335]: (B_1333='#skF_4' | k8_relset_1(A_1334, B_1333, C_1335, B_1333)=A_1334 | ~m1_subset_1(C_1335, k1_zfmisc_1(k2_zfmisc_1(A_1334, B_1333))) | ~v1_funct_2(C_1335, A_1334, B_1333) | ~v1_funct_1(C_1335))), inference(demodulation, [status(thm), theory('equality')], [c_34821, c_78])).
% 16.93/8.26  tff(c_35826, plain, (![B_1333, A_1334]: (B_1333='#skF_4' | k8_relset_1(A_1334, B_1333, '#skF_4', B_1333)=A_1334 | ~v1_funct_2('#skF_4', A_1334, B_1333) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34877, c_35820])).
% 16.93/8.26  tff(c_35833, plain, (![B_1333, A_1334]: (B_1333='#skF_4' | k8_relset_1(A_1334, B_1333, '#skF_4', B_1333)=A_1334 | ~v1_funct_2('#skF_4', A_1334, B_1333))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_35826])).
% 16.93/8.26  tff(c_43193, plain, (![B_1823, A_1824]: (B_1823='#skF_4' | A_1824='#skF_4' | ~v1_funct_2('#skF_4', A_1824, B_1823))), inference(demodulation, [status(thm), theory('equality')], [c_35788, c_35833])).
% 16.93/8.26  tff(c_43196, plain, ('#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_86, c_43193])).
% 16.93/8.26  tff(c_43200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35610, c_34881, c_43196])).
% 16.93/8.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.93/8.26  
% 16.93/8.26  Inference rules
% 16.93/8.26  ----------------------
% 16.93/8.26  #Ref     : 21
% 16.93/8.26  #Sup     : 10667
% 16.93/8.26  #Fact    : 1
% 16.93/8.26  #Define  : 0
% 16.93/8.26  #Split   : 28
% 16.93/8.26  #Chain   : 0
% 16.93/8.26  #Close   : 0
% 16.93/8.26  
% 16.93/8.26  Ordering : KBO
% 16.93/8.26  
% 16.93/8.26  Simplification rules
% 16.93/8.26  ----------------------
% 16.93/8.26  #Subsume      : 5712
% 16.93/8.26  #Demod        : 5446
% 16.93/8.26  #Tautology    : 3113
% 16.93/8.26  #SimpNegUnit  : 494
% 16.93/8.26  #BackRed      : 237
% 16.93/8.26  
% 16.93/8.26  #Partial instantiations: 0
% 16.93/8.26  #Strategies tried      : 1
% 16.93/8.26  
% 16.93/8.26  Timing (in seconds)
% 16.93/8.26  ----------------------
% 16.93/8.26  Preprocessing        : 0.37
% 16.93/8.26  Parsing              : 0.20
% 16.93/8.26  CNF conversion       : 0.02
% 16.93/8.26  Main loop            : 7.09
% 16.93/8.27  Inferencing          : 1.35
% 16.93/8.27  Reduction            : 2.85
% 16.93/8.27  Demodulation         : 2.28
% 16.93/8.27  BG Simplification    : 0.14
% 16.93/8.27  Subsumption          : 2.44
% 16.93/8.27  Abstraction          : 0.22
% 16.93/8.27  MUC search           : 0.00
% 16.93/8.27  Cooper               : 0.00
% 16.93/8.27  Total                : 7.51
% 16.93/8.27  Index Insertion      : 0.00
% 16.93/8.27  Index Deletion       : 0.00
% 16.93/8.27  Index Matching       : 0.00
% 16.93/8.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
