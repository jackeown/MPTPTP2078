%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:43 EST 2020

% Result     : Theorem 16.30s
% Output     : CNFRefutation 16.53s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 448 expanded)
%              Number of leaves         :   34 ( 165 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 (1116 expanded)
%              Number of equality atoms :   49 ( 368 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(c_76,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_53370,plain,(
    ! [A_841] :
      ( r1_tarski(A_841,k2_zfmisc_1(k1_relat_1(A_841),k2_relat_1(A_841)))
      | ~ v1_relat_1(A_841) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    ! [A_33] :
      ( r1_tarski(A_33,k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33)))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_316,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4614,plain,(
    ! [A_255,B_256,A_257] :
      ( k1_relset_1(A_255,B_256,A_257) = k1_relat_1(A_257)
      | ~ r1_tarski(A_257,k2_zfmisc_1(A_255,B_256)) ) ),
    inference(resolution,[status(thm)],[c_24,c_316])).

tff(c_4703,plain,(
    ! [A_33] :
      ( k1_relset_1(k1_relat_1(A_33),k2_relat_1(A_33),A_33) = k1_relat_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_40,c_4614])).

tff(c_2011,plain,(
    ! [B_161,C_162,A_163] :
      ( k1_xboole_0 = B_161
      | v1_funct_2(C_162,A_163,B_161)
      | k1_relset_1(A_163,B_161,C_162) != A_163
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_7441,plain,(
    ! [B_335,A_336,A_337] :
      ( k1_xboole_0 = B_335
      | v1_funct_2(A_336,A_337,B_335)
      | k1_relset_1(A_337,B_335,A_336) != A_337
      | ~ r1_tarski(A_336,k2_zfmisc_1(A_337,B_335)) ) ),
    inference(resolution,[status(thm)],[c_24,c_2011])).

tff(c_50579,plain,(
    ! [A_805] :
      ( k2_relat_1(A_805) = k1_xboole_0
      | v1_funct_2(A_805,k1_relat_1(A_805),k2_relat_1(A_805))
      | k1_relset_1(k1_relat_1(A_805),k2_relat_1(A_805),A_805) != k1_relat_1(A_805)
      | ~ v1_relat_1(A_805) ) ),
    inference(resolution,[status(thm)],[c_40,c_7441])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72])).

tff(c_104,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_50586,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50579,c_104])).

tff(c_50703,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_50586])).

tff(c_51096,plain,(
    k1_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50703])).

tff(c_51254,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4703,c_51096])).

tff(c_51258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_51254])).

tff(c_51259,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50703])).

tff(c_211,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,k2_zfmisc_1(k1_relat_1(A_83),k2_relat_1(A_83)))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_224,plain,(
    ! [A_83] :
      ( k2_zfmisc_1(k1_relat_1(A_83),k2_relat_1(A_83)) = A_83
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_83),k2_relat_1(A_83)),A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_211,c_8])).

tff(c_51391,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),k1_xboole_0),'#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_51259,c_224])).

tff(c_51511,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14,c_18,c_18,c_51259,c_51391])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    ! [A_37] : k1_relat_1(k6_relat_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ! [A_37] : k2_relat_1(k6_relat_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_219,plain,(
    ! [A_37] :
      ( r1_tarski(k6_relat_1(A_37),k2_zfmisc_1(k1_relat_1(k6_relat_1(A_37)),A_37))
      | ~ v1_relat_1(k6_relat_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_211])).

tff(c_229,plain,(
    ! [A_84] : r1_tarski(k6_relat_1(A_84),k2_zfmisc_1(A_84,A_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_219])).

tff(c_238,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_229])).

tff(c_165,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_170,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_165])).

tff(c_257,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_238,c_170])).

tff(c_272,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_46])).

tff(c_60,plain,(
    ! [A_48] :
      ( v1_funct_2(k1_xboole_0,A_48,k1_xboole_0)
      | k1_xboole_0 = A_48
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_48,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_81,plain,(
    ! [A_48] :
      ( v1_funct_2(k1_xboole_0,A_48,k1_xboole_0)
      | k1_xboole_0 = A_48
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_376,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_379,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_376])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_379])).

tff(c_385,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_3534,plain,(
    ! [B_215,C_216] :
      ( k1_relset_1(k1_xboole_0,B_215,C_216) = k1_relat_1(C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_316])).

tff(c_3536,plain,(
    ! [B_215] : k1_relset_1(k1_xboole_0,B_215,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_385,c_3534])).

tff(c_3541,plain,(
    ! [B_215] : k1_relset_1(k1_xboole_0,B_215,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_3536])).

tff(c_64,plain,(
    ! [C_50,B_49] :
      ( v1_funct_2(C_50,k1_xboole_0,B_49)
      | k1_relset_1(k1_xboole_0,B_49,C_50) != k1_xboole_0
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1541,plain,(
    ! [C_138,B_139] :
      ( v1_funct_2(C_138,k1_xboole_0,B_139)
      | k1_relset_1(k1_xboole_0,B_139,C_138) != k1_xboole_0
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_64])).

tff(c_1547,plain,(
    ! [B_139] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_139)
      | k1_relset_1(k1_xboole_0,B_139,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_385,c_1541])).

tff(c_3544,plain,(
    ! [B_139] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3541,c_1547])).

tff(c_51652,plain,(
    ! [B_139] : v1_funct_2('#skF_6','#skF_6',B_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51511,c_51511,c_3544])).

tff(c_51686,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51511,c_51511,c_272])).

tff(c_51261,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51259,c_104])).

tff(c_52110,plain,(
    ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51511,c_51261])).

tff(c_52299,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51686,c_52110])).

tff(c_53259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51652,c_52299])).

tff(c_53260,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_53348,plain,(
    ~ r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_24,c_53260])).

tff(c_53376,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_53370,c_53348])).

tff(c_53389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_53376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.30/7.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.53/7.42  
% 16.53/7.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.53/7.42  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 16.53/7.42  
% 16.53/7.42  %Foreground sorts:
% 16.53/7.42  
% 16.53/7.42  
% 16.53/7.42  %Background operators:
% 16.53/7.42  
% 16.53/7.42  
% 16.53/7.42  %Foreground operators:
% 16.53/7.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.53/7.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.53/7.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.53/7.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.53/7.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.53/7.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.53/7.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.53/7.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.53/7.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.53/7.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.53/7.42  tff('#skF_6', type, '#skF_6': $i).
% 16.53/7.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 16.53/7.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 16.53/7.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.53/7.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.53/7.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.53/7.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.53/7.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 16.53/7.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.53/7.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.53/7.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.53/7.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.53/7.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.53/7.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.53/7.42  
% 16.53/7.44  tff(f_139, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 16.53/7.44  tff(f_75, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 16.53/7.44  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.53/7.44  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.53/7.44  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 16.53/7.44  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 16.53/7.44  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 16.53/7.44  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.53/7.44  tff(f_94, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 16.53/7.44  tff(f_90, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 16.53/7.44  tff(c_76, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.53/7.44  tff(c_53370, plain, (![A_841]: (r1_tarski(A_841, k2_zfmisc_1(k1_relat_1(A_841), k2_relat_1(A_841))) | ~v1_relat_1(A_841))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.53/7.44  tff(c_24, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.53/7.44  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.53/7.44  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.53/7.44  tff(c_40, plain, (![A_33]: (r1_tarski(A_33, k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33))) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.53/7.44  tff(c_316, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.53/7.44  tff(c_4614, plain, (![A_255, B_256, A_257]: (k1_relset_1(A_255, B_256, A_257)=k1_relat_1(A_257) | ~r1_tarski(A_257, k2_zfmisc_1(A_255, B_256)))), inference(resolution, [status(thm)], [c_24, c_316])).
% 16.53/7.44  tff(c_4703, plain, (![A_33]: (k1_relset_1(k1_relat_1(A_33), k2_relat_1(A_33), A_33)=k1_relat_1(A_33) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_40, c_4614])).
% 16.53/7.44  tff(c_2011, plain, (![B_161, C_162, A_163]: (k1_xboole_0=B_161 | v1_funct_2(C_162, A_163, B_161) | k1_relset_1(A_163, B_161, C_162)!=A_163 | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_161))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 16.53/7.44  tff(c_7441, plain, (![B_335, A_336, A_337]: (k1_xboole_0=B_335 | v1_funct_2(A_336, A_337, B_335) | k1_relset_1(A_337, B_335, A_336)!=A_337 | ~r1_tarski(A_336, k2_zfmisc_1(A_337, B_335)))), inference(resolution, [status(thm)], [c_24, c_2011])).
% 16.53/7.44  tff(c_50579, plain, (![A_805]: (k2_relat_1(A_805)=k1_xboole_0 | v1_funct_2(A_805, k1_relat_1(A_805), k2_relat_1(A_805)) | k1_relset_1(k1_relat_1(A_805), k2_relat_1(A_805), A_805)!=k1_relat_1(A_805) | ~v1_relat_1(A_805))), inference(resolution, [status(thm)], [c_40, c_7441])).
% 16.53/7.44  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.53/7.44  tff(c_72, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 16.53/7.44  tff(c_78, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72])).
% 16.53/7.44  tff(c_104, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_78])).
% 16.53/7.44  tff(c_50586, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50579, c_104])).
% 16.53/7.44  tff(c_50703, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_50586])).
% 16.53/7.44  tff(c_51096, plain, (k1_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_50703])).
% 16.53/7.44  tff(c_51254, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4703, c_51096])).
% 16.53/7.44  tff(c_51258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_51254])).
% 16.53/7.44  tff(c_51259, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50703])).
% 16.53/7.44  tff(c_211, plain, (![A_83]: (r1_tarski(A_83, k2_zfmisc_1(k1_relat_1(A_83), k2_relat_1(A_83))) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.53/7.44  tff(c_8, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_tarski(B_5, A_4) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.53/7.44  tff(c_224, plain, (![A_83]: (k2_zfmisc_1(k1_relat_1(A_83), k2_relat_1(A_83))=A_83 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_83), k2_relat_1(A_83)), A_83) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_211, c_8])).
% 16.53/7.44  tff(c_51391, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))='#skF_6' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), k1_xboole_0), '#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_51259, c_224])).
% 16.53/7.44  tff(c_51511, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14, c_18, c_18, c_51259, c_51391])).
% 16.53/7.44  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.53/7.44  tff(c_50, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.53/7.44  tff(c_46, plain, (![A_37]: (k1_relat_1(k6_relat_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.53/7.44  tff(c_48, plain, (![A_37]: (k2_relat_1(k6_relat_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.53/7.44  tff(c_219, plain, (![A_37]: (r1_tarski(k6_relat_1(A_37), k2_zfmisc_1(k1_relat_1(k6_relat_1(A_37)), A_37)) | ~v1_relat_1(k6_relat_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_211])).
% 16.53/7.44  tff(c_229, plain, (![A_84]: (r1_tarski(k6_relat_1(A_84), k2_zfmisc_1(A_84, A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_219])).
% 16.53/7.44  tff(c_238, plain, (r1_tarski(k6_relat_1(k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_229])).
% 16.53/7.44  tff(c_165, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.53/7.44  tff(c_170, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_165])).
% 16.53/7.44  tff(c_257, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_238, c_170])).
% 16.53/7.44  tff(c_272, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_257, c_46])).
% 16.53/7.44  tff(c_60, plain, (![A_48]: (v1_funct_2(k1_xboole_0, A_48, k1_xboole_0) | k1_xboole_0=A_48 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_48, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 16.53/7.44  tff(c_81, plain, (![A_48]: (v1_funct_2(k1_xboole_0, A_48, k1_xboole_0) | k1_xboole_0=A_48 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 16.53/7.44  tff(c_376, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_81])).
% 16.53/7.44  tff(c_379, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_376])).
% 16.53/7.44  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_379])).
% 16.53/7.44  tff(c_385, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_81])).
% 16.53/7.44  tff(c_3534, plain, (![B_215, C_216]: (k1_relset_1(k1_xboole_0, B_215, C_216)=k1_relat_1(C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_316])).
% 16.53/7.44  tff(c_3536, plain, (![B_215]: (k1_relset_1(k1_xboole_0, B_215, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_385, c_3534])).
% 16.53/7.44  tff(c_3541, plain, (![B_215]: (k1_relset_1(k1_xboole_0, B_215, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_272, c_3536])).
% 16.53/7.44  tff(c_64, plain, (![C_50, B_49]: (v1_funct_2(C_50, k1_xboole_0, B_49) | k1_relset_1(k1_xboole_0, B_49, C_50)!=k1_xboole_0 | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_49))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 16.53/7.44  tff(c_1541, plain, (![C_138, B_139]: (v1_funct_2(C_138, k1_xboole_0, B_139) | k1_relset_1(k1_xboole_0, B_139, C_138)!=k1_xboole_0 | ~m1_subset_1(C_138, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_64])).
% 16.53/7.44  tff(c_1547, plain, (![B_139]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_139) | k1_relset_1(k1_xboole_0, B_139, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_385, c_1541])).
% 16.53/7.44  tff(c_3544, plain, (![B_139]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_139))), inference(demodulation, [status(thm), theory('equality')], [c_3541, c_1547])).
% 16.53/7.44  tff(c_51652, plain, (![B_139]: (v1_funct_2('#skF_6', '#skF_6', B_139))), inference(demodulation, [status(thm), theory('equality')], [c_51511, c_51511, c_3544])).
% 16.53/7.44  tff(c_51686, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_51511, c_51511, c_272])).
% 16.53/7.44  tff(c_51261, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51259, c_104])).
% 16.53/7.44  tff(c_52110, plain, (~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_51511, c_51261])).
% 16.53/7.44  tff(c_52299, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_51686, c_52110])).
% 16.53/7.44  tff(c_53259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51652, c_52299])).
% 16.53/7.44  tff(c_53260, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(splitRight, [status(thm)], [c_78])).
% 16.53/7.44  tff(c_53348, plain, (~r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_24, c_53260])).
% 16.53/7.44  tff(c_53376, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_53370, c_53348])).
% 16.53/7.44  tff(c_53389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_53376])).
% 16.53/7.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.53/7.44  
% 16.53/7.44  Inference rules
% 16.53/7.44  ----------------------
% 16.53/7.44  #Ref     : 0
% 16.53/7.44  #Sup     : 12992
% 16.53/7.44  #Fact    : 0
% 16.53/7.44  #Define  : 0
% 16.53/7.44  #Split   : 10
% 16.53/7.44  #Chain   : 0
% 16.53/7.44  #Close   : 0
% 16.53/7.44  
% 16.53/7.44  Ordering : KBO
% 16.53/7.44  
% 16.53/7.44  Simplification rules
% 16.53/7.44  ----------------------
% 16.53/7.44  #Subsume      : 6036
% 16.53/7.44  #Demod        : 12997
% 16.53/7.44  #Tautology    : 3930
% 16.53/7.44  #SimpNegUnit  : 217
% 16.53/7.44  #BackRed      : 214
% 16.53/7.44  
% 16.53/7.44  #Partial instantiations: 0
% 16.53/7.44  #Strategies tried      : 1
% 16.53/7.44  
% 16.53/7.44  Timing (in seconds)
% 16.53/7.44  ----------------------
% 16.53/7.44  Preprocessing        : 0.38
% 16.53/7.44  Parsing              : 0.19
% 16.53/7.44  CNF conversion       : 0.03
% 16.53/7.44  Main loop            : 6.26
% 16.53/7.44  Inferencing          : 1.12
% 16.53/7.44  Reduction            : 1.73
% 16.53/7.44  Demodulation         : 1.23
% 16.53/7.44  BG Simplification    : 0.13
% 16.53/7.44  Subsumption          : 2.90
% 16.53/7.44  Abstraction          : 0.23
% 16.53/7.44  MUC search           : 0.00
% 16.53/7.44  Cooper               : 0.00
% 16.53/7.44  Total                : 6.67
% 16.53/7.44  Index Insertion      : 0.00
% 16.53/7.44  Index Deletion       : 0.00
% 16.53/7.44  Index Matching       : 0.00
% 16.53/7.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
