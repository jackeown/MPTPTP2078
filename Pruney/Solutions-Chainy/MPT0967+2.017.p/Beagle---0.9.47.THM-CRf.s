%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:15 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 393 expanded)
%              Number of leaves         :   34 ( 140 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 (1159 expanded)
%              Number of equality atoms :   33 ( 396 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62])).

tff(c_150,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_714,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1(k2_relset_1(A_118,B_119,C_120),k1_zfmisc_1(B_119))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1259,plain,(
    ! [A_189,B_190,C_191] :
      ( r1_tarski(k2_relset_1(A_189,B_190,C_191),B_190)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(resolution,[status(thm)],[c_714,c_22])).

tff(c_1280,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1259])).

tff(c_66,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_342,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(A_77,C_78)
      | ~ r1_tarski(B_79,C_78)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_354,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,'#skF_3')
      | ~ r1_tarski(A_77,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_342])).

tff(c_1292,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1280,c_354])).

tff(c_56,plain,(
    ! [B_29,D_31,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | v1_funct_2(D_31,A_28,C_30)
      | ~ r1_tarski(k2_relset_1(A_28,B_29,D_31),C_30)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(D_31,A_28,B_29)
      | ~ v1_funct_1(D_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1448,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1292,c_56])).

tff(c_1457,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1448])).

tff(c_1459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_100,c_1457])).

tff(c_1460,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2046,plain,(
    ! [A_277,B_278,C_279] :
      ( m1_subset_1(k2_relset_1(A_277,B_278,C_279),k1_zfmisc_1(B_278))
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2707,plain,(
    ! [A_352,B_353,C_354] :
      ( r1_tarski(k2_relset_1(A_352,B_353,C_354),B_353)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_352,B_353))) ) ),
    inference(resolution,[status(thm)],[c_2046,c_22])).

tff(c_2728,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2707])).

tff(c_1639,plain,(
    ! [A_229,C_230,B_231] :
      ( r1_tarski(A_229,C_230)
      | ~ r1_tarski(B_231,C_230)
      | ~ r1_tarski(A_229,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1651,plain,(
    ! [A_229] :
      ( r1_tarski(A_229,'#skF_3')
      | ~ r1_tarski(A_229,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_1639])).

tff(c_2740,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2728,c_1651])).

tff(c_2980,plain,(
    ! [B_370,D_371,A_372,C_373] :
      ( k1_xboole_0 = B_370
      | m1_subset_1(D_371,k1_zfmisc_1(k2_zfmisc_1(A_372,C_373)))
      | ~ r1_tarski(k2_relset_1(A_372,B_370,D_371),C_373)
      | ~ m1_subset_1(D_371,k1_zfmisc_1(k2_zfmisc_1(A_372,B_370)))
      | ~ v1_funct_2(D_371,A_372,B_370)
      | ~ v1_funct_1(D_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2984,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2740,c_2980])).

tff(c_3003,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_2984])).

tff(c_3005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1460,c_100,c_3003])).

tff(c_3006,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_12,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3010,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3006,c_12])).

tff(c_18,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3008,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3006,c_3006,c_18])).

tff(c_3007,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3018,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3006,c_3007])).

tff(c_3063,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_3018,c_68])).

tff(c_3064,plain,(
    ! [A_378,B_379] :
      ( r1_tarski(A_378,B_379)
      | ~ m1_subset_1(A_378,k1_zfmisc_1(B_379)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3071,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_3063,c_3064])).

tff(c_3081,plain,(
    ! [B_382,A_383] :
      ( B_382 = A_383
      | ~ r1_tarski(B_382,A_383)
      | ~ r1_tarski(A_383,B_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3083,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_3071,c_3081])).

tff(c_3090,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3010,c_3083])).

tff(c_20,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3009,plain,(
    ! [A_9] : m1_subset_1('#skF_1',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3006,c_20])).

tff(c_3101,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3090,c_3009])).

tff(c_3174,plain,(
    ! [C_390,A_391,B_392] :
      ( v1_relat_1(C_390)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_391,B_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3187,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3101,c_3174])).

tff(c_3103,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3090,c_3010])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3011,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3006,c_3006,c_32])).

tff(c_3104,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3090,c_3090,c_3011])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3012,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3006,c_3006,c_34])).

tff(c_3102,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3090,c_3090,c_3012])).

tff(c_3477,plain,(
    ! [B_446,A_447] :
      ( v1_funct_2(B_446,k1_relat_1(B_446),A_447)
      | ~ r1_tarski(k2_relat_1(B_446),A_447)
      | ~ v1_funct_1(B_446)
      | ~ v1_relat_1(B_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3480,plain,(
    ! [A_447] :
      ( v1_funct_2('#skF_4','#skF_4',A_447)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_447)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3102,c_3477])).

tff(c_3482,plain,(
    ! [A_447] : v1_funct_2('#skF_4','#skF_4',A_447) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3187,c_72,c_3103,c_3104,c_3480])).

tff(c_3075,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_3008,c_74])).

tff(c_3097,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3090,c_3075])).

tff(c_3486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_3097])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.97  
% 4.76/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.97  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.76/1.97  
% 4.76/1.97  %Foreground sorts:
% 4.76/1.97  
% 4.76/1.97  
% 4.76/1.97  %Background operators:
% 4.76/1.97  
% 4.76/1.97  
% 4.76/1.97  %Foreground operators:
% 4.76/1.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.76/1.97  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.76/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.76/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.76/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.76/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.76/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.76/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.76/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.76/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.76/1.97  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.76/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.76/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.97  
% 4.76/1.99  tff(f_132, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 4.76/1.99  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.76/1.99  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.76/1.99  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.76/1.99  tff(f_112, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 4.76/1.99  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.76/1.99  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.76/1.99  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.76/1.99  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.76/1.99  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.76/1.99  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.76/1.99  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.76/1.99  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.76/1.99  tff(c_62, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.76/1.99  tff(c_74, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62])).
% 4.76/1.99  tff(c_150, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_74])).
% 4.76/1.99  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.76/1.99  tff(c_100, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 4.76/1.99  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.76/1.99  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.76/1.99  tff(c_714, plain, (![A_118, B_119, C_120]: (m1_subset_1(k2_relset_1(A_118, B_119, C_120), k1_zfmisc_1(B_119)) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.76/1.99  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.76/1.99  tff(c_1259, plain, (![A_189, B_190, C_191]: (r1_tarski(k2_relset_1(A_189, B_190, C_191), B_190) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(resolution, [status(thm)], [c_714, c_22])).
% 4.76/1.99  tff(c_1280, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1259])).
% 4.76/1.99  tff(c_66, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.76/1.99  tff(c_342, plain, (![A_77, C_78, B_79]: (r1_tarski(A_77, C_78) | ~r1_tarski(B_79, C_78) | ~r1_tarski(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.76/1.99  tff(c_354, plain, (![A_77]: (r1_tarski(A_77, '#skF_3') | ~r1_tarski(A_77, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_342])).
% 4.76/1.99  tff(c_1292, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1280, c_354])).
% 4.76/1.99  tff(c_56, plain, (![B_29, D_31, A_28, C_30]: (k1_xboole_0=B_29 | v1_funct_2(D_31, A_28, C_30) | ~r1_tarski(k2_relset_1(A_28, B_29, D_31), C_30) | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(D_31, A_28, B_29) | ~v1_funct_1(D_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.76/1.99  tff(c_1448, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1292, c_56])).
% 4.76/1.99  tff(c_1457, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1448])).
% 4.76/1.99  tff(c_1459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_100, c_1457])).
% 4.76/1.99  tff(c_1460, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_74])).
% 4.76/1.99  tff(c_2046, plain, (![A_277, B_278, C_279]: (m1_subset_1(k2_relset_1(A_277, B_278, C_279), k1_zfmisc_1(B_278)) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.76/1.99  tff(c_2707, plain, (![A_352, B_353, C_354]: (r1_tarski(k2_relset_1(A_352, B_353, C_354), B_353) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_352, B_353))))), inference(resolution, [status(thm)], [c_2046, c_22])).
% 4.76/1.99  tff(c_2728, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_68, c_2707])).
% 4.76/1.99  tff(c_1639, plain, (![A_229, C_230, B_231]: (r1_tarski(A_229, C_230) | ~r1_tarski(B_231, C_230) | ~r1_tarski(A_229, B_231))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.76/1.99  tff(c_1651, plain, (![A_229]: (r1_tarski(A_229, '#skF_3') | ~r1_tarski(A_229, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_1639])).
% 4.76/1.99  tff(c_2740, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2728, c_1651])).
% 4.76/1.99  tff(c_2980, plain, (![B_370, D_371, A_372, C_373]: (k1_xboole_0=B_370 | m1_subset_1(D_371, k1_zfmisc_1(k2_zfmisc_1(A_372, C_373))) | ~r1_tarski(k2_relset_1(A_372, B_370, D_371), C_373) | ~m1_subset_1(D_371, k1_zfmisc_1(k2_zfmisc_1(A_372, B_370))) | ~v1_funct_2(D_371, A_372, B_370) | ~v1_funct_1(D_371))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.76/1.99  tff(c_2984, plain, (k1_xboole_0='#skF_2' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2740, c_2980])).
% 4.76/1.99  tff(c_3003, plain, (k1_xboole_0='#skF_2' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_2984])).
% 4.76/1.99  tff(c_3005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1460, c_100, c_3003])).
% 4.76/1.99  tff(c_3006, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 4.76/1.99  tff(c_12, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.76/1.99  tff(c_3010, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3006, c_12])).
% 4.76/1.99  tff(c_18, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.76/1.99  tff(c_3008, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3006, c_3006, c_18])).
% 4.76/1.99  tff(c_3007, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 4.76/1.99  tff(c_3018, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3006, c_3007])).
% 4.76/1.99  tff(c_3063, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_3018, c_68])).
% 4.76/1.99  tff(c_3064, plain, (![A_378, B_379]: (r1_tarski(A_378, B_379) | ~m1_subset_1(A_378, k1_zfmisc_1(B_379)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.76/1.99  tff(c_3071, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_3063, c_3064])).
% 4.76/1.99  tff(c_3081, plain, (![B_382, A_383]: (B_382=A_383 | ~r1_tarski(B_382, A_383) | ~r1_tarski(A_383, B_382))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.76/1.99  tff(c_3083, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_3071, c_3081])).
% 4.76/1.99  tff(c_3090, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3010, c_3083])).
% 4.76/1.99  tff(c_20, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.76/1.99  tff(c_3009, plain, (![A_9]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_3006, c_20])).
% 4.76/1.99  tff(c_3101, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_3090, c_3009])).
% 4.76/1.99  tff(c_3174, plain, (![C_390, A_391, B_392]: (v1_relat_1(C_390) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_391, B_392))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.76/1.99  tff(c_3187, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3101, c_3174])).
% 4.76/1.99  tff(c_3103, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3090, c_3010])).
% 4.76/1.99  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.76/1.99  tff(c_3011, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3006, c_3006, c_32])).
% 4.76/1.99  tff(c_3104, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3090, c_3090, c_3011])).
% 4.76/1.99  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.76/1.99  tff(c_3012, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3006, c_3006, c_34])).
% 4.76/1.99  tff(c_3102, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3090, c_3090, c_3012])).
% 4.76/1.99  tff(c_3477, plain, (![B_446, A_447]: (v1_funct_2(B_446, k1_relat_1(B_446), A_447) | ~r1_tarski(k2_relat_1(B_446), A_447) | ~v1_funct_1(B_446) | ~v1_relat_1(B_446))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.76/1.99  tff(c_3480, plain, (![A_447]: (v1_funct_2('#skF_4', '#skF_4', A_447) | ~r1_tarski(k2_relat_1('#skF_4'), A_447) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3102, c_3477])).
% 4.76/1.99  tff(c_3482, plain, (![A_447]: (v1_funct_2('#skF_4', '#skF_4', A_447))), inference(demodulation, [status(thm), theory('equality')], [c_3187, c_72, c_3103, c_3104, c_3480])).
% 4.76/1.99  tff(c_3075, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_3008, c_74])).
% 4.76/1.99  tff(c_3097, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3090, c_3075])).
% 4.76/1.99  tff(c_3486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3482, c_3097])).
% 4.76/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.99  
% 4.76/1.99  Inference rules
% 4.76/1.99  ----------------------
% 4.76/1.99  #Ref     : 0
% 4.76/1.99  #Sup     : 719
% 4.76/1.99  #Fact    : 0
% 4.76/1.99  #Define  : 0
% 4.76/1.99  #Split   : 10
% 4.76/1.99  #Chain   : 0
% 4.76/1.99  #Close   : 0
% 4.76/1.99  
% 4.76/1.99  Ordering : KBO
% 4.76/1.99  
% 4.76/1.99  Simplification rules
% 4.76/1.99  ----------------------
% 4.76/1.99  #Subsume      : 130
% 4.76/1.99  #Demod        : 765
% 4.76/1.99  #Tautology    : 290
% 4.76/1.99  #SimpNegUnit  : 8
% 4.76/1.99  #BackRed      : 24
% 4.76/1.99  
% 4.76/1.99  #Partial instantiations: 0
% 4.76/1.99  #Strategies tried      : 1
% 4.76/1.99  
% 4.76/1.99  Timing (in seconds)
% 4.76/1.99  ----------------------
% 5.12/1.99  Preprocessing        : 0.33
% 5.12/1.99  Parsing              : 0.18
% 5.12/1.99  CNF conversion       : 0.02
% 5.12/1.99  Main loop            : 0.87
% 5.12/1.99  Inferencing          : 0.31
% 5.12/1.99  Reduction            : 0.30
% 5.12/1.99  Demodulation         : 0.22
% 5.12/1.99  BG Simplification    : 0.03
% 5.12/1.99  Subsumption          : 0.16
% 5.12/1.99  Abstraction          : 0.03
% 5.12/1.99  MUC search           : 0.00
% 5.12/1.99  Cooper               : 0.00
% 5.12/1.99  Total                : 1.24
% 5.12/1.99  Index Insertion      : 0.00
% 5.12/1.99  Index Deletion       : 0.00
% 5.12/1.99  Index Matching       : 0.00
% 5.12/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
