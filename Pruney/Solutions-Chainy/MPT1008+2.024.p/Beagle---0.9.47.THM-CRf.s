%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:29 EST 2020

% Result     : Theorem 17.66s
% Output     : CNFRefutation 17.89s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 349 expanded)
%              Number of leaves         :   43 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  225 ( 760 expanded)
%              Number of equality atoms :  119 ( 357 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
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

tff(f_92,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_139,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_113,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_203,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_216,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_203])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    ! [A_26] :
      ( k1_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_225,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_216,c_56])).

tff(c_241,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_665,plain,(
    ! [B_160,A_161] :
      ( k1_tarski(k1_funct_1(B_160,A_161)) = k2_relat_1(B_160)
      | k1_tarski(A_161) != k1_relat_1(B_160)
      | ~ v1_funct_1(B_160)
      | ~ v1_relat_1(B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_634,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(A_155,B_156,C_157) = k2_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_650,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_634])).

tff(c_72,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_660,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_72])).

tff(c_671,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_660])).

tff(c_693,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_80,c_671])).

tff(c_324,plain,(
    ! [C_103,A_104,B_105] :
      ( v4_relat_1(C_103,A_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_337,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_324])).

tff(c_48,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(B_25),A_24)
      | ~ v4_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_872,plain,(
    ! [A_192,B_193,C_194,D_195] :
      ( k1_enumset1(A_192,B_193,C_194) = D_195
      | k2_tarski(A_192,C_194) = D_195
      | k2_tarski(B_193,C_194) = D_195
      | k2_tarski(A_192,B_193) = D_195
      | k1_tarski(C_194) = D_195
      | k1_tarski(B_193) = D_195
      | k1_tarski(A_192) = D_195
      | k1_xboole_0 = D_195
      | ~ r1_tarski(D_195,k1_enumset1(A_192,B_193,C_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_901,plain,(
    ! [A_9,B_10,D_195] :
      ( k1_enumset1(A_9,A_9,B_10) = D_195
      | k2_tarski(A_9,B_10) = D_195
      | k2_tarski(A_9,B_10) = D_195
      | k2_tarski(A_9,A_9) = D_195
      | k1_tarski(B_10) = D_195
      | k1_tarski(A_9) = D_195
      | k1_tarski(A_9) = D_195
      | k1_xboole_0 = D_195
      | ~ r1_tarski(D_195,k2_tarski(A_9,B_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_872])).

tff(c_3004,plain,(
    ! [A_381,B_382,D_383] :
      ( k2_tarski(A_381,B_382) = D_383
      | k2_tarski(A_381,B_382) = D_383
      | k2_tarski(A_381,B_382) = D_383
      | k1_tarski(A_381) = D_383
      | k1_tarski(B_382) = D_383
      | k1_tarski(A_381) = D_383
      | k1_tarski(A_381) = D_383
      | k1_xboole_0 = D_383
      | ~ r1_tarski(D_383,k2_tarski(A_381,B_382)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_901])).

tff(c_3041,plain,(
    ! [A_8,D_383] :
      ( k2_tarski(A_8,A_8) = D_383
      | k2_tarski(A_8,A_8) = D_383
      | k2_tarski(A_8,A_8) = D_383
      | k1_tarski(A_8) = D_383
      | k1_tarski(A_8) = D_383
      | k1_tarski(A_8) = D_383
      | k1_tarski(A_8) = D_383
      | k1_xboole_0 = D_383
      | ~ r1_tarski(D_383,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3004])).

tff(c_10941,plain,(
    ! [A_669,D_670] :
      ( k1_tarski(A_669) = D_670
      | k1_tarski(A_669) = D_670
      | k1_tarski(A_669) = D_670
      | k1_tarski(A_669) = D_670
      | k1_tarski(A_669) = D_670
      | k1_tarski(A_669) = D_670
      | k1_tarski(A_669) = D_670
      | k1_xboole_0 = D_670
      | ~ r1_tarski(D_670,k1_tarski(A_669)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_14,c_3041])).

tff(c_11007,plain,(
    ! [A_671,B_672] :
      ( k1_tarski(A_671) = k1_relat_1(B_672)
      | k1_relat_1(B_672) = k1_xboole_0
      | ~ v4_relat_1(B_672,k1_tarski(A_671))
      | ~ v1_relat_1(B_672) ) ),
    inference(resolution,[status(thm)],[c_48,c_10941])).

tff(c_11076,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_337,c_11007])).

tff(c_11109,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_11076])).

tff(c_11111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_693,c_11109])).

tff(c_11112,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11122,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11112,c_11112,c_50])).

tff(c_54,plain,(
    ! [A_26] :
      ( k2_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_224,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_216,c_54])).

tff(c_240,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_11114,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11112,c_240])).

tff(c_11146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11122,c_11114])).

tff(c_11147,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11167,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_11147,c_52])).

tff(c_11148,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_11175,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_11148])).

tff(c_11498,plain,(
    ! [B_747,A_748] :
      ( k1_tarski(k1_funct_1(B_747,A_748)) = k2_relat_1(B_747)
      | k1_tarski(A_748) != k1_relat_1(B_747)
      | ~ v1_funct_1(B_747)
      | ~ v1_relat_1(B_747) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_11166,plain,(
    ! [A_18] : m1_subset_1('#skF_4',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_38])).

tff(c_11477,plain,(
    ! [A_740,B_741,C_742] :
      ( k2_relset_1(A_740,B_741,C_742) = k2_relat_1(C_742)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1(A_740,B_741))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_11481,plain,(
    ! [A_740,B_741] : k2_relset_1(A_740,B_741,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11166,c_11477])).

tff(c_11487,plain,(
    ! [A_740,B_741] : k2_relset_1(A_740,B_741,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11175,c_11481])).

tff(c_11489,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11487,c_72])).

tff(c_11504,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11498,c_11489])).

tff(c_11525,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_80,c_11167,c_11175,c_11504])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_11169,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_74])).

tff(c_78,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_157,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_11163,plain,(
    ! [A_18] : r1_tarski('#skF_4',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_157])).

tff(c_70,plain,(
    ! [D_43,C_42,A_40,B_41] :
      ( r2_hidden(k1_funct_1(D_43,C_42),k2_relset_1(A_40,B_41,D_43))
      | k1_xboole_0 = B_41
      | ~ r2_hidden(C_42,A_40)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(D_43,A_40,B_41)
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_11603,plain,(
    ! [D_755,C_756,A_757,B_758] :
      ( r2_hidden(k1_funct_1(D_755,C_756),k2_relset_1(A_757,B_758,D_755))
      | B_758 = '#skF_4'
      | ~ r2_hidden(C_756,A_757)
      | ~ m1_subset_1(D_755,k1_zfmisc_1(k2_zfmisc_1(A_757,B_758)))
      | ~ v1_funct_2(D_755,A_757,B_758)
      | ~ v1_funct_1(D_755) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_70])).

tff(c_60,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62301,plain,(
    ! [A_1887,B_1888,D_1889,C_1890] :
      ( ~ r1_tarski(k2_relset_1(A_1887,B_1888,D_1889),k1_funct_1(D_1889,C_1890))
      | B_1888 = '#skF_4'
      | ~ r2_hidden(C_1890,A_1887)
      | ~ m1_subset_1(D_1889,k1_zfmisc_1(k2_zfmisc_1(A_1887,B_1888)))
      | ~ v1_funct_2(D_1889,A_1887,B_1888)
      | ~ v1_funct_1(D_1889) ) ),
    inference(resolution,[status(thm)],[c_11603,c_60])).

tff(c_62322,plain,(
    ! [C_1890,B_741,A_740] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_1890))
      | B_741 = '#skF_4'
      | ~ r2_hidden(C_1890,A_740)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_740,B_741)))
      | ~ v1_funct_2('#skF_4',A_740,B_741)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11487,c_62301])).

tff(c_62326,plain,(
    ! [B_1891,C_1892,A_1893] :
      ( B_1891 = '#skF_4'
      | ~ r2_hidden(C_1892,A_1893)
      | ~ v1_funct_2('#skF_4',A_1893,B_1891) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11166,c_11163,c_62322])).

tff(c_62375,plain,(
    ! [B_1894,A_1895,B_1896] :
      ( B_1894 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_1895,B_1894)
      | r1_tarski(A_1895,B_1896) ) ),
    inference(resolution,[status(thm)],[c_6,c_62326])).

tff(c_62377,plain,(
    ! [B_1896] :
      ( '#skF_3' = '#skF_4'
      | r1_tarski(k1_tarski('#skF_2'),B_1896) ) ),
    inference(resolution,[status(thm)],[c_78,c_62375])).

tff(c_62381,plain,(
    ! [B_1897] : r1_tarski(k1_tarski('#skF_2'),B_1897) ),
    inference(negUnitSimplification,[status(thm)],[c_11169,c_62377])).

tff(c_162,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ r1_tarski(B_77,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_177,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_157,c_162])).

tff(c_11162,plain,(
    ! [A_18] :
      ( A_18 = '#skF_4'
      | ~ r1_tarski(A_18,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_11147,c_177])).

tff(c_62533,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62381,c_11162])).

tff(c_62601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11525,c_62533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.66/9.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.66/9.61  
% 17.66/9.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.66/9.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 17.66/9.61  
% 17.66/9.61  %Foreground sorts:
% 17.66/9.61  
% 17.66/9.61  
% 17.66/9.61  %Background operators:
% 17.66/9.61  
% 17.66/9.61  
% 17.66/9.61  %Foreground operators:
% 17.66/9.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 17.66/9.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.66/9.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.66/9.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.66/9.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.66/9.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.66/9.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.66/9.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.66/9.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.66/9.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.66/9.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.66/9.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.66/9.61  tff('#skF_2', type, '#skF_2': $i).
% 17.66/9.61  tff('#skF_3', type, '#skF_3': $i).
% 17.66/9.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 17.66/9.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.66/9.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 17.66/9.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.66/9.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.66/9.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.66/9.61  tff('#skF_4', type, '#skF_4': $i).
% 17.66/9.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.66/9.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 17.66/9.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.66/9.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.66/9.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.66/9.61  
% 17.89/9.63  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 17.89/9.63  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 17.89/9.63  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 17.89/9.63  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 17.89/9.63  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 17.89/9.63  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 17.89/9.63  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 17.89/9.63  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 17.89/9.63  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 17.89/9.63  tff(f_71, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 17.89/9.63  tff(f_92, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 17.89/9.63  tff(f_73, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 17.89/9.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.89/9.63  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.89/9.63  tff(f_139, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 17.89/9.63  tff(f_113, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 17.89/9.63  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.89/9.63  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 17.89/9.63  tff(c_203, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 17.89/9.63  tff(c_216, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_203])).
% 17.89/9.63  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 17.89/9.63  tff(c_56, plain, (![A_26]: (k1_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.89/9.63  tff(c_225, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_216, c_56])).
% 17.89/9.63  tff(c_241, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_225])).
% 17.89/9.63  tff(c_665, plain, (![B_160, A_161]: (k1_tarski(k1_funct_1(B_160, A_161))=k2_relat_1(B_160) | k1_tarski(A_161)!=k1_relat_1(B_160) | ~v1_funct_1(B_160) | ~v1_relat_1(B_160))), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.89/9.63  tff(c_634, plain, (![A_155, B_156, C_157]: (k2_relset_1(A_155, B_156, C_157)=k2_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 17.89/9.63  tff(c_650, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_634])).
% 17.89/9.63  tff(c_72, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 17.89/9.63  tff(c_660, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_650, c_72])).
% 17.89/9.63  tff(c_671, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_665, c_660])).
% 17.89/9.63  tff(c_693, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_80, c_671])).
% 17.89/9.63  tff(c_324, plain, (![C_103, A_104, B_105]: (v4_relat_1(C_103, A_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 17.89/9.63  tff(c_337, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_324])).
% 17.89/9.63  tff(c_48, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(B_25), A_24) | ~v4_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.89/9.63  tff(c_14, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.89/9.63  tff(c_16, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.89/9.63  tff(c_872, plain, (![A_192, B_193, C_194, D_195]: (k1_enumset1(A_192, B_193, C_194)=D_195 | k2_tarski(A_192, C_194)=D_195 | k2_tarski(B_193, C_194)=D_195 | k2_tarski(A_192, B_193)=D_195 | k1_tarski(C_194)=D_195 | k1_tarski(B_193)=D_195 | k1_tarski(A_192)=D_195 | k1_xboole_0=D_195 | ~r1_tarski(D_195, k1_enumset1(A_192, B_193, C_194)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.89/9.63  tff(c_901, plain, (![A_9, B_10, D_195]: (k1_enumset1(A_9, A_9, B_10)=D_195 | k2_tarski(A_9, B_10)=D_195 | k2_tarski(A_9, B_10)=D_195 | k2_tarski(A_9, A_9)=D_195 | k1_tarski(B_10)=D_195 | k1_tarski(A_9)=D_195 | k1_tarski(A_9)=D_195 | k1_xboole_0=D_195 | ~r1_tarski(D_195, k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_872])).
% 17.89/9.63  tff(c_3004, plain, (![A_381, B_382, D_383]: (k2_tarski(A_381, B_382)=D_383 | k2_tarski(A_381, B_382)=D_383 | k2_tarski(A_381, B_382)=D_383 | k1_tarski(A_381)=D_383 | k1_tarski(B_382)=D_383 | k1_tarski(A_381)=D_383 | k1_tarski(A_381)=D_383 | k1_xboole_0=D_383 | ~r1_tarski(D_383, k2_tarski(A_381, B_382)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_901])).
% 17.89/9.63  tff(c_3041, plain, (![A_8, D_383]: (k2_tarski(A_8, A_8)=D_383 | k2_tarski(A_8, A_8)=D_383 | k2_tarski(A_8, A_8)=D_383 | k1_tarski(A_8)=D_383 | k1_tarski(A_8)=D_383 | k1_tarski(A_8)=D_383 | k1_tarski(A_8)=D_383 | k1_xboole_0=D_383 | ~r1_tarski(D_383, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3004])).
% 17.89/9.63  tff(c_10941, plain, (![A_669, D_670]: (k1_tarski(A_669)=D_670 | k1_tarski(A_669)=D_670 | k1_tarski(A_669)=D_670 | k1_tarski(A_669)=D_670 | k1_tarski(A_669)=D_670 | k1_tarski(A_669)=D_670 | k1_tarski(A_669)=D_670 | k1_xboole_0=D_670 | ~r1_tarski(D_670, k1_tarski(A_669)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_14, c_3041])).
% 17.89/9.63  tff(c_11007, plain, (![A_671, B_672]: (k1_tarski(A_671)=k1_relat_1(B_672) | k1_relat_1(B_672)=k1_xboole_0 | ~v4_relat_1(B_672, k1_tarski(A_671)) | ~v1_relat_1(B_672))), inference(resolution, [status(thm)], [c_48, c_10941])).
% 17.89/9.63  tff(c_11076, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_337, c_11007])).
% 17.89/9.63  tff(c_11109, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_216, c_11076])).
% 17.89/9.63  tff(c_11111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_693, c_11109])).
% 17.89/9.63  tff(c_11112, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_225])).
% 17.89/9.63  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.89/9.63  tff(c_11122, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11112, c_11112, c_50])).
% 17.89/9.63  tff(c_54, plain, (![A_26]: (k2_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.89/9.63  tff(c_224, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_216, c_54])).
% 17.89/9.63  tff(c_240, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_224])).
% 17.89/9.63  tff(c_11114, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11112, c_240])).
% 17.89/9.63  tff(c_11146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11122, c_11114])).
% 17.89/9.63  tff(c_11147, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_224])).
% 17.89/9.63  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.89/9.63  tff(c_11167, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_11147, c_52])).
% 17.89/9.63  tff(c_11148, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_224])).
% 17.89/9.63  tff(c_11175, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_11148])).
% 17.89/9.63  tff(c_11498, plain, (![B_747, A_748]: (k1_tarski(k1_funct_1(B_747, A_748))=k2_relat_1(B_747) | k1_tarski(A_748)!=k1_relat_1(B_747) | ~v1_funct_1(B_747) | ~v1_relat_1(B_747))), inference(cnfTransformation, [status(thm)], [f_108])).
% 17.89/9.63  tff(c_38, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.89/9.63  tff(c_11166, plain, (![A_18]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_38])).
% 17.89/9.63  tff(c_11477, plain, (![A_740, B_741, C_742]: (k2_relset_1(A_740, B_741, C_742)=k2_relat_1(C_742) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1(A_740, B_741))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 17.89/9.63  tff(c_11481, plain, (![A_740, B_741]: (k2_relset_1(A_740, B_741, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11166, c_11477])).
% 17.89/9.63  tff(c_11487, plain, (![A_740, B_741]: (k2_relset_1(A_740, B_741, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11175, c_11481])).
% 17.89/9.63  tff(c_11489, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11487, c_72])).
% 17.89/9.63  tff(c_11504, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11498, c_11489])).
% 17.89/9.63  tff(c_11525, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_80, c_11167, c_11175, c_11504])).
% 17.89/9.63  tff(c_74, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_151])).
% 17.89/9.63  tff(c_11169, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_74])).
% 17.89/9.63  tff(c_78, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 17.89/9.63  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.89/9.63  tff(c_145, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.89/9.63  tff(c_157, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_38, c_145])).
% 17.89/9.63  tff(c_11163, plain, (![A_18]: (r1_tarski('#skF_4', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_157])).
% 17.89/9.63  tff(c_70, plain, (![D_43, C_42, A_40, B_41]: (r2_hidden(k1_funct_1(D_43, C_42), k2_relset_1(A_40, B_41, D_43)) | k1_xboole_0=B_41 | ~r2_hidden(C_42, A_40) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_139])).
% 17.89/9.63  tff(c_11603, plain, (![D_755, C_756, A_757, B_758]: (r2_hidden(k1_funct_1(D_755, C_756), k2_relset_1(A_757, B_758, D_755)) | B_758='#skF_4' | ~r2_hidden(C_756, A_757) | ~m1_subset_1(D_755, k1_zfmisc_1(k2_zfmisc_1(A_757, B_758))) | ~v1_funct_2(D_755, A_757, B_758) | ~v1_funct_1(D_755))), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_70])).
% 17.89/9.63  tff(c_60, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_113])).
% 17.89/9.63  tff(c_62301, plain, (![A_1887, B_1888, D_1889, C_1890]: (~r1_tarski(k2_relset_1(A_1887, B_1888, D_1889), k1_funct_1(D_1889, C_1890)) | B_1888='#skF_4' | ~r2_hidden(C_1890, A_1887) | ~m1_subset_1(D_1889, k1_zfmisc_1(k2_zfmisc_1(A_1887, B_1888))) | ~v1_funct_2(D_1889, A_1887, B_1888) | ~v1_funct_1(D_1889))), inference(resolution, [status(thm)], [c_11603, c_60])).
% 17.89/9.63  tff(c_62322, plain, (![C_1890, B_741, A_740]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_1890)) | B_741='#skF_4' | ~r2_hidden(C_1890, A_740) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_740, B_741))) | ~v1_funct_2('#skF_4', A_740, B_741) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11487, c_62301])).
% 17.89/9.63  tff(c_62326, plain, (![B_1891, C_1892, A_1893]: (B_1891='#skF_4' | ~r2_hidden(C_1892, A_1893) | ~v1_funct_2('#skF_4', A_1893, B_1891))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11166, c_11163, c_62322])).
% 17.89/9.63  tff(c_62375, plain, (![B_1894, A_1895, B_1896]: (B_1894='#skF_4' | ~v1_funct_2('#skF_4', A_1895, B_1894) | r1_tarski(A_1895, B_1896))), inference(resolution, [status(thm)], [c_6, c_62326])).
% 17.89/9.63  tff(c_62377, plain, (![B_1896]: ('#skF_3'='#skF_4' | r1_tarski(k1_tarski('#skF_2'), B_1896))), inference(resolution, [status(thm)], [c_78, c_62375])).
% 17.89/9.63  tff(c_62381, plain, (![B_1897]: (r1_tarski(k1_tarski('#skF_2'), B_1897))), inference(negUnitSimplification, [status(thm)], [c_11169, c_62377])).
% 17.89/9.63  tff(c_162, plain, (![B_77, A_78]: (B_77=A_78 | ~r1_tarski(B_77, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.89/9.63  tff(c_177, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_157, c_162])).
% 17.89/9.63  tff(c_11162, plain, (![A_18]: (A_18='#skF_4' | ~r1_tarski(A_18, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_11147, c_177])).
% 17.89/9.63  tff(c_62533, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_62381, c_11162])).
% 17.89/9.63  tff(c_62601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11525, c_62533])).
% 17.89/9.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.89/9.63  
% 17.89/9.63  Inference rules
% 17.89/9.63  ----------------------
% 17.89/9.63  #Ref     : 0
% 17.89/9.63  #Sup     : 14422
% 17.89/9.63  #Fact    : 0
% 17.89/9.63  #Define  : 0
% 17.89/9.63  #Split   : 18
% 17.89/9.63  #Chain   : 0
% 17.89/9.63  #Close   : 0
% 17.89/9.63  
% 17.89/9.63  Ordering : KBO
% 17.89/9.63  
% 17.89/9.63  Simplification rules
% 17.89/9.63  ----------------------
% 17.89/9.63  #Subsume      : 4681
% 17.89/9.63  #Demod        : 15666
% 17.89/9.63  #Tautology    : 5279
% 17.89/9.63  #SimpNegUnit  : 14
% 17.89/9.63  #BackRed      : 48
% 17.89/9.63  
% 17.89/9.63  #Partial instantiations: 0
% 17.89/9.63  #Strategies tried      : 1
% 17.89/9.63  
% 17.89/9.63  Timing (in seconds)
% 17.89/9.63  ----------------------
% 17.89/9.63  Preprocessing        : 0.44
% 17.89/9.63  Parsing              : 0.26
% 17.89/9.63  CNF conversion       : 0.02
% 17.89/9.63  Main loop            : 8.30
% 17.89/9.63  Inferencing          : 1.61
% 17.89/9.63  Reduction            : 2.70
% 17.89/9.63  Demodulation         : 2.08
% 17.89/9.63  BG Simplification    : 0.17
% 17.89/9.63  Subsumption          : 3.43
% 17.89/9.63  Abstraction          : 0.30
% 17.89/9.63  MUC search           : 0.00
% 17.89/9.63  Cooper               : 0.00
% 17.89/9.63  Total                : 8.77
% 17.89/9.63  Index Insertion      : 0.00
% 17.89/9.63  Index Deletion       : 0.00
% 17.89/9.63  Index Matching       : 0.00
% 17.89/9.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
