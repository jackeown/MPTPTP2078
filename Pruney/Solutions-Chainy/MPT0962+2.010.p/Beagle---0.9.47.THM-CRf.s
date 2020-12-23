%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:52 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  155 (1241 expanded)
%              Number of leaves         :   29 ( 414 expanded)
%              Depth                    :   15
%              Number of atoms          :  279 (2960 expanded)
%              Number of equality atoms :   59 ( 605 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5617,plain,(
    ! [C_500,A_501,B_502] :
      ( m1_subset_1(C_500,k1_zfmisc_1(k2_zfmisc_1(A_501,B_502)))
      | ~ r1_tarski(k2_relat_1(C_500),B_502)
      | ~ r1_tarski(k1_relat_1(C_500),A_501)
      | ~ v1_relat_1(C_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_94,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_394,plain,(
    ! [C_82,A_83,B_84] :
      ( m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ r1_tarski(k2_relat_1(C_82),B_84)
      | ~ r1_tarski(k1_relat_1(C_82),A_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1497,plain,(
    ! [C_194,A_195,B_196] :
      ( r1_tarski(C_194,k2_zfmisc_1(A_195,B_196))
      | ~ r1_tarski(k2_relat_1(C_194),B_196)
      | ~ r1_tarski(k1_relat_1(C_194),A_195)
      | ~ v1_relat_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_394,c_14])).

tff(c_1499,plain,(
    ! [A_195] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_195,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_195)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_1497])).

tff(c_1511,plain,(
    ! [A_197] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_197,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1499])).

tff(c_1523,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1511])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_283,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_294,plain,(
    ! [A_70,B_71,A_5] :
      ( k1_relset_1(A_70,B_71,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_70,B_71)) ) ),
    inference(resolution,[status(thm)],[c_16,c_283])).

tff(c_1538,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1523,c_294])).

tff(c_666,plain,(
    ! [B_121,C_122,A_123] :
      ( k1_xboole_0 = B_121
      | v1_funct_2(C_122,A_123,B_121)
      | k1_relset_1(A_123,B_121,C_122) != A_123
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2170,plain,(
    ! [B_229,A_230,A_231] :
      ( k1_xboole_0 = B_229
      | v1_funct_2(A_230,A_231,B_229)
      | k1_relset_1(A_231,B_229,A_230) != A_231
      | ~ r1_tarski(A_230,k2_zfmisc_1(A_231,B_229)) ) ),
    inference(resolution,[status(thm)],[c_16,c_666])).

tff(c_2179,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1523,c_2170])).

tff(c_2202,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1538,c_2179])).

tff(c_2203,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2202])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_270,plain,(
    ! [C_66,A_67] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_197])).

tff(c_275,plain,(
    ! [A_68,A_69] :
      ( v4_relat_1(A_68,A_69)
      | ~ r1_tarski(A_68,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_270])).

tff(c_100,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,(
    ! [C_34] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_100])).

tff(c_116,plain,(
    ! [A_35] :
      ( v1_relat_1(A_35)
      | ~ r1_tarski(A_35,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_110])).

tff(c_121,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_223,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k1_relat_1(B_63),A_64)
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_239,plain,(
    ! [A_64] :
      ( r1_tarski(k1_xboole_0,A_64)
      | ~ v4_relat_1(k1_xboole_0,A_64)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_223])).

tff(c_245,plain,(
    ! [A_64] :
      ( r1_tarski(k1_xboole_0,A_64)
      | ~ v4_relat_1(k1_xboole_0,A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_239])).

tff(c_279,plain,(
    ! [A_69] :
      ( r1_tarski(k1_xboole_0,A_69)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_275,c_245])).

tff(c_282,plain,(
    ! [A_69] : r1_tarski(k1_xboole_0,A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_279])).

tff(c_2259,plain,(
    ! [A_69] : r1_tarski('#skF_1',A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2203,c_282])).

tff(c_122,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_132,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_2369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2259,c_132])).

tff(c_2370,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_2407,plain,(
    ! [C_240,A_241,B_242] :
      ( v4_relat_1(C_240,A_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2437,plain,(
    ! [C_247,A_248] :
      ( v4_relat_1(C_247,A_248)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2407])).

tff(c_2441,plain,(
    ! [A_5,A_248] :
      ( v4_relat_1(A_5,A_248)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_2437])).

tff(c_2443,plain,(
    ! [B_251,A_252] :
      ( r1_tarski(k1_relat_1(B_251),A_252)
      | ~ v4_relat_1(B_251,A_252)
      | ~ v1_relat_1(B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2459,plain,(
    ! [A_252] :
      ( r1_tarski(k1_xboole_0,A_252)
      | ~ v4_relat_1(k1_xboole_0,A_252)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2443])).

tff(c_2466,plain,(
    ! [A_253] :
      ( r1_tarski(k1_xboole_0,A_253)
      | ~ v4_relat_1(k1_xboole_0,A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_2459])).

tff(c_2470,plain,(
    ! [A_248] :
      ( r1_tarski(k1_xboole_0,A_248)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2441,c_2466])).

tff(c_2483,plain,(
    ! [A_248] : r1_tarski(k1_xboole_0,A_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2470])).

tff(c_2692,plain,(
    ! [C_285,A_286,B_287] :
      ( m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ r1_tarski(k2_relat_1(C_285),B_287)
      | ~ r1_tarski(k1_relat_1(C_285),A_286)
      | ~ v1_relat_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3863,plain,(
    ! [C_392,A_393,B_394] :
      ( r1_tarski(C_392,k2_zfmisc_1(A_393,B_394))
      | ~ r1_tarski(k2_relat_1(C_392),B_394)
      | ~ r1_tarski(k1_relat_1(C_392),A_393)
      | ~ v1_relat_1(C_392) ) ),
    inference(resolution,[status(thm)],[c_2692,c_14])).

tff(c_3876,plain,(
    ! [C_395,A_396] :
      ( r1_tarski(C_395,k2_zfmisc_1(A_396,k2_relat_1(C_395)))
      | ~ r1_tarski(k1_relat_1(C_395),A_396)
      | ~ v1_relat_1(C_395) ) ),
    inference(resolution,[status(thm)],[c_6,c_3863])).

tff(c_3903,plain,(
    ! [A_396] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_396,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_396)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2370,c_3876])).

tff(c_3948,plain,(
    ! [A_398] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_398,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3903])).

tff(c_3973,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_3948])).

tff(c_2582,plain,(
    ! [A_267,B_268,C_269] :
      ( k1_relset_1(A_267,B_268,C_269) = k1_relat_1(C_269)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2593,plain,(
    ! [A_267,B_268,A_5] :
      ( k1_relset_1(A_267,B_268,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_267,B_268)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2582])).

tff(c_4010,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3973,c_2593])).

tff(c_2841,plain,(
    ! [B_304,C_305,A_306] :
      ( k1_xboole_0 = B_304
      | v1_funct_2(C_305,A_306,B_304)
      | k1_relset_1(A_306,B_304,C_305) != A_306
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4173,plain,(
    ! [B_410,A_411,A_412] :
      ( k1_xboole_0 = B_410
      | v1_funct_2(A_411,A_412,B_410)
      | k1_relset_1(A_412,B_410,A_411) != A_412
      | ~ r1_tarski(A_411,k2_zfmisc_1(A_412,B_410)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2841])).

tff(c_4185,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3973,c_4173])).

tff(c_4212,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4010,c_4185])).

tff(c_4213,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4212])).

tff(c_3576,plain,(
    ! [C_383,A_384] :
      ( m1_subset_1(C_383,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_383),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_383),A_384)
      | ~ v1_relat_1(C_383) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2692])).

tff(c_3578,plain,(
    ! [A_384] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_384)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2370,c_3576])).

tff(c_3582,plain,(
    ! [A_384] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3578])).

tff(c_3585,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3582])).

tff(c_4227,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4213,c_3585])).

tff(c_4280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4227])).

tff(c_4282,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3582])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4294,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_4282,c_2])).

tff(c_4304,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2483,c_4294])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3428,plain,(
    ! [C_374,B_375] :
      ( m1_subset_1(C_374,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_374),B_375)
      | ~ r1_tarski(k1_relat_1(C_374),k1_xboole_0)
      | ~ v1_relat_1(C_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2692])).

tff(c_3431,plain,(
    ! [B_375] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',B_375)
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2370,c_3428])).

tff(c_3439,plain,(
    ! [B_375] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',B_375)
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3431])).

tff(c_3484,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3439])).

tff(c_3487,plain,
    ( ~ v4_relat_1('#skF_2',k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_3484])).

tff(c_3490,plain,(
    ~ v4_relat_1('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3487])).

tff(c_3494,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2441,c_3490])).

tff(c_4483,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_3494])).

tff(c_4281,plain,(
    ! [A_384] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_384)
      | m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_3582])).

tff(c_4465,plain,(
    ! [A_419] : ~ r1_tarski(k1_relat_1('#skF_2'),A_419) ),
    inference(splitLeft,[status(thm)],[c_4281])).

tff(c_4477,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_4465])).

tff(c_4478,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4281])).

tff(c_4637,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4304,c_4478])).

tff(c_4644,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_4637,c_14])).

tff(c_4646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4483,c_4644])).

tff(c_4648,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3439])).

tff(c_3440,plain,(
    ! [C_374] :
      ( m1_subset_1(C_374,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_374),k1_xboole_0)
      | ~ v1_relat_1(C_374) ) ),
    inference(resolution,[status(thm)],[c_6,c_3428])).

tff(c_4651,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4648,c_3440])).

tff(c_4672,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4651])).

tff(c_4838,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4672,c_14])).

tff(c_4866,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_4838,c_2])).

tff(c_4880,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2483,c_4866])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4930,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4880,c_22])).

tff(c_4936,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2370,c_4930])).

tff(c_2875,plain,(
    ! [A_311,B_312,A_313] :
      ( k1_relset_1(A_311,B_312,A_313) = k1_relat_1(A_313)
      | ~ r1_tarski(A_313,k2_zfmisc_1(A_311,B_312)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2582])).

tff(c_2879,plain,(
    ! [A_311,B_312] : k1_relset_1(A_311,B_312,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2483,c_2875])).

tff(c_2895,plain,(
    ! [A_311,B_312] : k1_relset_1(A_311,B_312,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2879])).

tff(c_36,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_21,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_36])).

tff(c_2554,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_2557,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_2554])).

tff(c_2561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2557])).

tff(c_2563,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_40,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2924,plain,(
    ! [C_318,B_319] :
      ( v1_funct_2(C_318,k1_xboole_0,B_319)
      | k1_relset_1(k1_xboole_0,B_319,C_318) != k1_xboole_0
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_2926,plain,(
    ! [B_319] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_319)
      | k1_relset_1(k1_xboole_0,B_319,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2563,c_2924])).

tff(c_2932,plain,(
    ! [B_319] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_319) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2895,c_2926])).

tff(c_4900,plain,(
    ! [B_319] : v1_funct_2('#skF_2','#skF_2',B_319) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4880,c_2932])).

tff(c_5289,plain,(
    ! [B_319] : v1_funct_2('#skF_1','#skF_1',B_319) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4936,c_4936,c_4900])).

tff(c_4666,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4648,c_2])).

tff(c_4682,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2483,c_4666])).

tff(c_4701,plain,(
    ~ v1_funct_2('#skF_2',k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4682,c_94])).

tff(c_4885,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4701])).

tff(c_5056,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4936,c_4936,c_4885])).

tff(c_5292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5289,c_5056])).

tff(c_5293,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5632,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5617,c_5293])).

tff(c_5649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_50,c_5632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.12  
% 5.78/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.12  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.78/2.12  
% 5.78/2.12  %Foreground sorts:
% 5.78/2.12  
% 5.78/2.12  
% 5.78/2.12  %Background operators:
% 5.78/2.12  
% 5.78/2.12  
% 5.78/2.12  %Foreground operators:
% 5.78/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.78/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.78/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.78/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.78/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.78/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.78/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.78/2.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.78/2.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.78/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.78/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.78/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.78/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.78/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.78/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.78/2.12  
% 5.78/2.15  tff(f_103, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.78/2.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.78/2.15  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.78/2.15  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.78/2.15  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.78/2.15  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.78/2.15  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.78/2.15  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.78/2.15  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.78/2.15  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.78/2.15  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.78/2.15  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.78/2.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.15  tff(c_50, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.78/2.15  tff(c_5617, plain, (![C_500, A_501, B_502]: (m1_subset_1(C_500, k1_zfmisc_1(k2_zfmisc_1(A_501, B_502))) | ~r1_tarski(k2_relat_1(C_500), B_502) | ~r1_tarski(k1_relat_1(C_500), A_501) | ~v1_relat_1(C_500))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.78/2.15  tff(c_52, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.78/2.15  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.78/2.15  tff(c_56, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 5.78/2.15  tff(c_94, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 5.78/2.15  tff(c_394, plain, (![C_82, A_83, B_84]: (m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~r1_tarski(k2_relat_1(C_82), B_84) | ~r1_tarski(k1_relat_1(C_82), A_83) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.78/2.15  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.78/2.15  tff(c_1497, plain, (![C_194, A_195, B_196]: (r1_tarski(C_194, k2_zfmisc_1(A_195, B_196)) | ~r1_tarski(k2_relat_1(C_194), B_196) | ~r1_tarski(k1_relat_1(C_194), A_195) | ~v1_relat_1(C_194))), inference(resolution, [status(thm)], [c_394, c_14])).
% 5.78/2.15  tff(c_1499, plain, (![A_195]: (r1_tarski('#skF_2', k2_zfmisc_1(A_195, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_195) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_1497])).
% 5.78/2.15  tff(c_1511, plain, (![A_197]: (r1_tarski('#skF_2', k2_zfmisc_1(A_197, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_197))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1499])).
% 5.78/2.15  tff(c_1523, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1511])).
% 5.78/2.15  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.78/2.15  tff(c_283, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.78/2.15  tff(c_294, plain, (![A_70, B_71, A_5]: (k1_relset_1(A_70, B_71, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_70, B_71)))), inference(resolution, [status(thm)], [c_16, c_283])).
% 5.78/2.15  tff(c_1538, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1523, c_294])).
% 5.78/2.15  tff(c_666, plain, (![B_121, C_122, A_123]: (k1_xboole_0=B_121 | v1_funct_2(C_122, A_123, B_121) | k1_relset_1(A_123, B_121, C_122)!=A_123 | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_121))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.78/2.15  tff(c_2170, plain, (![B_229, A_230, A_231]: (k1_xboole_0=B_229 | v1_funct_2(A_230, A_231, B_229) | k1_relset_1(A_231, B_229, A_230)!=A_231 | ~r1_tarski(A_230, k2_zfmisc_1(A_231, B_229)))), inference(resolution, [status(thm)], [c_16, c_666])).
% 5.78/2.15  tff(c_2179, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1523, c_2170])).
% 5.78/2.15  tff(c_2202, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1538, c_2179])).
% 5.78/2.15  tff(c_2203, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_94, c_2202])).
% 5.78/2.15  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.78/2.15  tff(c_197, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.78/2.15  tff(c_270, plain, (![C_66, A_67]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_197])).
% 5.78/2.15  tff(c_275, plain, (![A_68, A_69]: (v4_relat_1(A_68, A_69) | ~r1_tarski(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_270])).
% 5.78/2.15  tff(c_100, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.78/2.15  tff(c_110, plain, (![C_34]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_100])).
% 5.78/2.15  tff(c_116, plain, (![A_35]: (v1_relat_1(A_35) | ~r1_tarski(A_35, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_110])).
% 5.78/2.15  tff(c_121, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_116])).
% 5.78/2.15  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.78/2.15  tff(c_223, plain, (![B_63, A_64]: (r1_tarski(k1_relat_1(B_63), A_64) | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.15  tff(c_239, plain, (![A_64]: (r1_tarski(k1_xboole_0, A_64) | ~v4_relat_1(k1_xboole_0, A_64) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_223])).
% 5.78/2.15  tff(c_245, plain, (![A_64]: (r1_tarski(k1_xboole_0, A_64) | ~v4_relat_1(k1_xboole_0, A_64))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_239])).
% 5.78/2.15  tff(c_279, plain, (![A_69]: (r1_tarski(k1_xboole_0, A_69) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_275, c_245])).
% 5.78/2.15  tff(c_282, plain, (![A_69]: (r1_tarski(k1_xboole_0, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_279])).
% 5.78/2.15  tff(c_2259, plain, (![A_69]: (r1_tarski('#skF_1', A_69))), inference(demodulation, [status(thm), theory('equality')], [c_2203, c_282])).
% 5.78/2.15  tff(c_122, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.15  tff(c_127, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_122])).
% 5.78/2.15  tff(c_132, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_127])).
% 5.78/2.15  tff(c_2369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2259, c_132])).
% 5.78/2.15  tff(c_2370, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_127])).
% 5.78/2.15  tff(c_2407, plain, (![C_240, A_241, B_242]: (v4_relat_1(C_240, A_241) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.78/2.15  tff(c_2437, plain, (![C_247, A_248]: (v4_relat_1(C_247, A_248) | ~m1_subset_1(C_247, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2407])).
% 5.78/2.15  tff(c_2441, plain, (![A_5, A_248]: (v4_relat_1(A_5, A_248) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_2437])).
% 5.78/2.15  tff(c_2443, plain, (![B_251, A_252]: (r1_tarski(k1_relat_1(B_251), A_252) | ~v4_relat_1(B_251, A_252) | ~v1_relat_1(B_251))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.15  tff(c_2459, plain, (![A_252]: (r1_tarski(k1_xboole_0, A_252) | ~v4_relat_1(k1_xboole_0, A_252) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2443])).
% 5.78/2.15  tff(c_2466, plain, (![A_253]: (r1_tarski(k1_xboole_0, A_253) | ~v4_relat_1(k1_xboole_0, A_253))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_2459])).
% 5.78/2.15  tff(c_2470, plain, (![A_248]: (r1_tarski(k1_xboole_0, A_248) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_2441, c_2466])).
% 5.78/2.15  tff(c_2483, plain, (![A_248]: (r1_tarski(k1_xboole_0, A_248))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2470])).
% 5.78/2.15  tff(c_2692, plain, (![C_285, A_286, B_287]: (m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~r1_tarski(k2_relat_1(C_285), B_287) | ~r1_tarski(k1_relat_1(C_285), A_286) | ~v1_relat_1(C_285))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.78/2.15  tff(c_3863, plain, (![C_392, A_393, B_394]: (r1_tarski(C_392, k2_zfmisc_1(A_393, B_394)) | ~r1_tarski(k2_relat_1(C_392), B_394) | ~r1_tarski(k1_relat_1(C_392), A_393) | ~v1_relat_1(C_392))), inference(resolution, [status(thm)], [c_2692, c_14])).
% 5.78/2.15  tff(c_3876, plain, (![C_395, A_396]: (r1_tarski(C_395, k2_zfmisc_1(A_396, k2_relat_1(C_395))) | ~r1_tarski(k1_relat_1(C_395), A_396) | ~v1_relat_1(C_395))), inference(resolution, [status(thm)], [c_6, c_3863])).
% 5.78/2.15  tff(c_3903, plain, (![A_396]: (r1_tarski('#skF_2', k2_zfmisc_1(A_396, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_396) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2370, c_3876])).
% 5.78/2.15  tff(c_3948, plain, (![A_398]: (r1_tarski('#skF_2', k2_zfmisc_1(A_398, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_398))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3903])).
% 5.78/2.15  tff(c_3973, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_3948])).
% 5.78/2.15  tff(c_2582, plain, (![A_267, B_268, C_269]: (k1_relset_1(A_267, B_268, C_269)=k1_relat_1(C_269) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.78/2.15  tff(c_2593, plain, (![A_267, B_268, A_5]: (k1_relset_1(A_267, B_268, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_267, B_268)))), inference(resolution, [status(thm)], [c_16, c_2582])).
% 5.78/2.15  tff(c_4010, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3973, c_2593])).
% 5.78/2.15  tff(c_2841, plain, (![B_304, C_305, A_306]: (k1_xboole_0=B_304 | v1_funct_2(C_305, A_306, B_304) | k1_relset_1(A_306, B_304, C_305)!=A_306 | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_304))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.78/2.15  tff(c_4173, plain, (![B_410, A_411, A_412]: (k1_xboole_0=B_410 | v1_funct_2(A_411, A_412, B_410) | k1_relset_1(A_412, B_410, A_411)!=A_412 | ~r1_tarski(A_411, k2_zfmisc_1(A_412, B_410)))), inference(resolution, [status(thm)], [c_16, c_2841])).
% 5.78/2.15  tff(c_4185, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3973, c_4173])).
% 5.78/2.15  tff(c_4212, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4010, c_4185])).
% 5.78/2.15  tff(c_4213, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_94, c_4212])).
% 5.78/2.15  tff(c_3576, plain, (![C_383, A_384]: (m1_subset_1(C_383, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_383), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_383), A_384) | ~v1_relat_1(C_383))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2692])).
% 5.78/2.15  tff(c_3578, plain, (![A_384]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_384) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2370, c_3576])).
% 5.78/2.15  tff(c_3582, plain, (![A_384]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_384))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3578])).
% 5.78/2.15  tff(c_3585, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3582])).
% 5.78/2.15  tff(c_4227, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4213, c_3585])).
% 5.78/2.15  tff(c_4280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4227])).
% 5.78/2.15  tff(c_4282, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3582])).
% 5.78/2.15  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.15  tff(c_4294, plain, (k1_xboole_0='#skF_1' | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_4282, c_2])).
% 5.78/2.15  tff(c_4304, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2483, c_4294])).
% 5.78/2.15  tff(c_20, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.15  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.78/2.15  tff(c_3428, plain, (![C_374, B_375]: (m1_subset_1(C_374, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_374), B_375) | ~r1_tarski(k1_relat_1(C_374), k1_xboole_0) | ~v1_relat_1(C_374))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2692])).
% 5.78/2.15  tff(c_3431, plain, (![B_375]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', B_375) | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2370, c_3428])).
% 5.78/2.15  tff(c_3439, plain, (![B_375]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', B_375) | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3431])).
% 5.78/2.15  tff(c_3484, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3439])).
% 5.78/2.15  tff(c_3487, plain, (~v4_relat_1('#skF_2', k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_3484])).
% 5.78/2.15  tff(c_3490, plain, (~v4_relat_1('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3487])).
% 5.78/2.15  tff(c_3494, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_2441, c_3490])).
% 5.78/2.15  tff(c_4483, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_3494])).
% 5.78/2.15  tff(c_4281, plain, (![A_384]: (~r1_tarski(k1_relat_1('#skF_2'), A_384) | m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_3582])).
% 5.78/2.15  tff(c_4465, plain, (![A_419]: (~r1_tarski(k1_relat_1('#skF_2'), A_419))), inference(splitLeft, [status(thm)], [c_4281])).
% 5.78/2.15  tff(c_4477, plain, $false, inference(resolution, [status(thm)], [c_6, c_4465])).
% 5.78/2.15  tff(c_4478, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_4281])).
% 5.78/2.15  tff(c_4637, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4304, c_4478])).
% 5.78/2.15  tff(c_4644, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_4637, c_14])).
% 5.78/2.15  tff(c_4646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4483, c_4644])).
% 5.78/2.15  tff(c_4648, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_3439])).
% 5.78/2.15  tff(c_3440, plain, (![C_374]: (m1_subset_1(C_374, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_374), k1_xboole_0) | ~v1_relat_1(C_374))), inference(resolution, [status(thm)], [c_6, c_3428])).
% 5.78/2.15  tff(c_4651, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4648, c_3440])).
% 5.78/2.15  tff(c_4672, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4651])).
% 5.78/2.15  tff(c_4838, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_4672, c_14])).
% 5.78/2.15  tff(c_4866, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_4838, c_2])).
% 5.78/2.15  tff(c_4880, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2483, c_4866])).
% 5.78/2.15  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.78/2.15  tff(c_4930, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4880, c_22])).
% 5.78/2.15  tff(c_4936, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2370, c_4930])).
% 5.78/2.15  tff(c_2875, plain, (![A_311, B_312, A_313]: (k1_relset_1(A_311, B_312, A_313)=k1_relat_1(A_313) | ~r1_tarski(A_313, k2_zfmisc_1(A_311, B_312)))), inference(resolution, [status(thm)], [c_16, c_2582])).
% 5.78/2.15  tff(c_2879, plain, (![A_311, B_312]: (k1_relset_1(A_311, B_312, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2483, c_2875])).
% 5.78/2.15  tff(c_2895, plain, (![A_311, B_312]: (k1_relset_1(A_311, B_312, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2879])).
% 5.78/2.15  tff(c_36, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_21, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.78/2.15  tff(c_60, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_36])).
% 5.78/2.15  tff(c_2554, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_60])).
% 5.78/2.15  tff(c_2557, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_2554])).
% 5.78/2.15  tff(c_2561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2557])).
% 5.78/2.15  tff(c_2563, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_60])).
% 5.78/2.15  tff(c_40, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.78/2.15  tff(c_2924, plain, (![C_318, B_319]: (v1_funct_2(C_318, k1_xboole_0, B_319) | k1_relset_1(k1_xboole_0, B_319, C_318)!=k1_xboole_0 | ~m1_subset_1(C_318, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 5.78/2.15  tff(c_2926, plain, (![B_319]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_319) | k1_relset_1(k1_xboole_0, B_319, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2563, c_2924])).
% 5.78/2.15  tff(c_2932, plain, (![B_319]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_319))), inference(demodulation, [status(thm), theory('equality')], [c_2895, c_2926])).
% 5.78/2.15  tff(c_4900, plain, (![B_319]: (v1_funct_2('#skF_2', '#skF_2', B_319))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4880, c_2932])).
% 5.78/2.15  tff(c_5289, plain, (![B_319]: (v1_funct_2('#skF_1', '#skF_1', B_319))), inference(demodulation, [status(thm), theory('equality')], [c_4936, c_4936, c_4900])).
% 5.78/2.15  tff(c_4666, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4648, c_2])).
% 5.78/2.15  tff(c_4682, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2483, c_4666])).
% 5.78/2.15  tff(c_4701, plain, (~v1_funct_2('#skF_2', k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4682, c_94])).
% 5.78/2.15  tff(c_4885, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4701])).
% 5.78/2.15  tff(c_5056, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4936, c_4936, c_4885])).
% 5.78/2.15  tff(c_5292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5289, c_5056])).
% 5.78/2.15  tff(c_5293, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 5.78/2.15  tff(c_5632, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5617, c_5293])).
% 5.78/2.15  tff(c_5649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_50, c_5632])).
% 5.78/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.15  
% 5.78/2.15  Inference rules
% 5.78/2.15  ----------------------
% 5.78/2.15  #Ref     : 0
% 5.78/2.15  #Sup     : 1133
% 5.78/2.15  #Fact    : 0
% 5.78/2.15  #Define  : 0
% 5.78/2.15  #Split   : 16
% 5.78/2.15  #Chain   : 0
% 5.78/2.15  #Close   : 0
% 5.78/2.15  
% 5.78/2.15  Ordering : KBO
% 5.78/2.15  
% 5.78/2.15  Simplification rules
% 5.78/2.15  ----------------------
% 5.78/2.15  #Subsume      : 148
% 5.78/2.15  #Demod        : 1833
% 5.78/2.15  #Tautology    : 587
% 5.78/2.15  #SimpNegUnit  : 11
% 5.78/2.15  #BackRed      : 287
% 5.78/2.15  
% 5.78/2.15  #Partial instantiations: 0
% 5.78/2.15  #Strategies tried      : 1
% 5.78/2.15  
% 5.78/2.15  Timing (in seconds)
% 5.78/2.15  ----------------------
% 5.78/2.15  Preprocessing        : 0.31
% 5.78/2.15  Parsing              : 0.16
% 5.78/2.15  CNF conversion       : 0.02
% 5.78/2.15  Main loop            : 1.03
% 5.78/2.15  Inferencing          : 0.35
% 5.78/2.15  Reduction            : 0.37
% 5.78/2.15  Demodulation         : 0.27
% 5.78/2.15  BG Simplification    : 0.04
% 5.78/2.15  Subsumption          : 0.19
% 5.78/2.15  Abstraction          : 0.05
% 5.78/2.15  MUC search           : 0.00
% 5.78/2.15  Cooper               : 0.00
% 5.78/2.15  Total                : 1.39
% 5.78/2.15  Index Insertion      : 0.00
% 5.78/2.15  Index Deletion       : 0.00
% 5.78/2.15  Index Matching       : 0.00
% 5.78/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
