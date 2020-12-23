%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:52 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 724 expanded)
%              Number of leaves         :   29 ( 250 expanded)
%              Depth                    :   14
%              Number of atoms          :  260 (1710 expanded)
%              Number of equality atoms :   59 ( 382 expanded)
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

tff(f_104,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5412,plain,(
    ! [C_503,A_504,B_505] :
      ( m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_505)))
      | ~ r1_tarski(k2_relat_1(C_503),B_505)
      | ~ r1_tarski(k1_relat_1(C_503),A_504)
      | ~ v1_relat_1(C_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46])).

tff(c_96,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_345,plain,(
    ! [C_83,A_84,B_85] :
      ( m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ r1_tarski(k2_relat_1(C_83),B_85)
      | ~ r1_tarski(k1_relat_1(C_83),A_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1428,plain,(
    ! [C_189,A_190,B_191] :
      ( r1_tarski(C_189,k2_zfmisc_1(A_190,B_191))
      | ~ r1_tarski(k2_relat_1(C_189),B_191)
      | ~ r1_tarski(k1_relat_1(C_189),A_190)
      | ~ v1_relat_1(C_189) ) ),
    inference(resolution,[status(thm)],[c_345,c_16])).

tff(c_1430,plain,(
    ! [A_190] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_190,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_190)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_1428])).

tff(c_1438,plain,(
    ! [A_192] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_192,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1430])).

tff(c_1450,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1438])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_257,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_268,plain,(
    ! [A_74,B_75,A_6] :
      ( k1_relset_1(A_74,B_75,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_74,B_75)) ) ),
    inference(resolution,[status(thm)],[c_18,c_257])).

tff(c_1465,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1450,c_268])).

tff(c_625,plain,(
    ! [B_117,C_118,A_119] :
      ( k1_xboole_0 = B_117
      | v1_funct_2(C_118,A_119,B_117)
      | k1_relset_1(A_119,B_117,C_118) != A_119
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2110,plain,(
    ! [B_228,A_229,A_230] :
      ( k1_xboole_0 = B_228
      | v1_funct_2(A_229,A_230,B_228)
      | k1_relset_1(A_230,B_228,A_229) != A_230
      | ~ r1_tarski(A_229,k2_zfmisc_1(A_230,B_228)) ) ),
    inference(resolution,[status(thm)],[c_18,c_625])).

tff(c_2119,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1450,c_2110])).

tff(c_2142,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_2119])).

tff(c_2143,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2142])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_234,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_269,plain,(
    ! [A_77,A_78,B_79] :
      ( v4_relat_1(A_77,A_78)
      | ~ r1_tarski(A_77,k2_zfmisc_1(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_18,c_234])).

tff(c_286,plain,(
    ! [A_80,B_81] : v4_relat_1(k2_zfmisc_1(A_80,B_81),A_80) ),
    inference(resolution,[status(thm)],[c_6,c_269])).

tff(c_293,plain,(
    ! [A_4] : v4_relat_1(k1_xboole_0,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_286])).

tff(c_119,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_129,plain,(
    ! [C_40] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_119])).

tff(c_135,plain,(
    ! [A_41] :
      ( v1_relat_1(A_41)
      | ~ r1_tarski(A_41,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_129])).

tff(c_140,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_195,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_222,plain,(
    ! [B_60] :
      ( k1_relat_1(B_60) = k1_xboole_0
      | ~ v4_relat_1(B_60,k1_xboole_0)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_195,c_8])).

tff(c_290,plain,(
    ! [B_81] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_81)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_81)) ) ),
    inference(resolution,[status(thm)],[c_286,c_222])).

tff(c_299,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_14,c_14,c_290])).

tff(c_22,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_306,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | ~ v4_relat_1(k1_xboole_0,A_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_22])).

tff(c_318,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | ~ v4_relat_1(k1_xboole_0,A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_306])).

tff(c_392,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_318])).

tff(c_2192,plain,(
    ! [A_8] : r1_tarski('#skF_1',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2143,c_392])).

tff(c_97,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_97])).

tff(c_107,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_2217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2192,c_107])).

tff(c_2218,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_2543,plain,(
    ! [C_284,A_285,B_286] :
      ( m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ r1_tarski(k2_relat_1(C_284),B_286)
      | ~ r1_tarski(k1_relat_1(C_284),A_285)
      | ~ v1_relat_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3961,plain,(
    ! [C_409,A_410,B_411] :
      ( r1_tarski(C_409,k2_zfmisc_1(A_410,B_411))
      | ~ r1_tarski(k2_relat_1(C_409),B_411)
      | ~ r1_tarski(k1_relat_1(C_409),A_410)
      | ~ v1_relat_1(C_409) ) ),
    inference(resolution,[status(thm)],[c_2543,c_16])).

tff(c_3970,plain,(
    ! [C_412,A_413] :
      ( r1_tarski(C_412,k2_zfmisc_1(A_413,k2_relat_1(C_412)))
      | ~ r1_tarski(k1_relat_1(C_412),A_413)
      | ~ v1_relat_1(C_412) ) ),
    inference(resolution,[status(thm)],[c_6,c_3961])).

tff(c_3997,plain,(
    ! [A_413] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_413,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_413)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2218,c_3970])).

tff(c_4037,plain,(
    ! [A_415] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_415,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_415) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3997])).

tff(c_4062,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_4037])).

tff(c_2463,plain,(
    ! [A_271,B_272,C_273] :
      ( k1_relset_1(A_271,B_272,C_273) = k1_relat_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2474,plain,(
    ! [A_271,B_272,A_6] :
      ( k1_relset_1(A_271,B_272,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_271,B_272)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2463])).

tff(c_4099,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4062,c_2474])).

tff(c_2682,plain,(
    ! [B_305,C_306,A_307] :
      ( k1_xboole_0 = B_305
      | v1_funct_2(C_306,A_307,B_305)
      | k1_relset_1(A_307,B_305,C_306) != A_307
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_307,B_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4164,plain,(
    ! [B_420,A_421,A_422] :
      ( k1_xboole_0 = B_420
      | v1_funct_2(A_421,A_422,B_420)
      | k1_relset_1(A_422,B_420,A_421) != A_422
      | ~ r1_tarski(A_421,k2_zfmisc_1(A_422,B_420)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2682])).

tff(c_4173,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4062,c_4164])).

tff(c_4199,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4099,c_4173])).

tff(c_4200,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_4199])).

tff(c_3247,plain,(
    ! [C_373,A_374] :
      ( m1_subset_1(C_373,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_373),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_373),A_374)
      | ~ v1_relat_1(C_373) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2543])).

tff(c_3249,plain,(
    ! [A_374] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_374)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2218,c_3247])).

tff(c_3251,plain,(
    ! [A_374] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3249])).

tff(c_3252,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3251])).

tff(c_4229,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4200,c_3252])).

tff(c_4273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4229])).

tff(c_4275,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3251])).

tff(c_4298,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4275,c_8])).

tff(c_2227,plain,(
    ! [C_231,A_232,B_233] :
      ( v1_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2237,plain,(
    ! [C_234] :
      ( v1_relat_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2227])).

tff(c_2243,plain,(
    ! [A_235] :
      ( v1_relat_1(A_235)
      | ~ r1_tarski(A_235,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_2237])).

tff(c_2248,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_2243])).

tff(c_2277,plain,(
    ! [C_243,A_244,B_245] :
      ( v4_relat_1(C_243,A_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2295,plain,(
    ! [A_250,A_251,B_252] :
      ( v4_relat_1(A_250,A_251)
      | ~ r1_tarski(A_250,k2_zfmisc_1(A_251,B_252)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2277])).

tff(c_2306,plain,(
    ! [A_251,B_252] : v4_relat_1(k2_zfmisc_1(A_251,B_252),A_251) ),
    inference(resolution,[status(thm)],[c_6,c_2295])).

tff(c_2323,plain,(
    ! [B_259,A_260] :
      ( r1_tarski(k1_relat_1(B_259),A_260)
      | ~ v4_relat_1(B_259,A_260)
      | ~ v1_relat_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2351,plain,(
    ! [B_261] :
      ( k1_relat_1(B_261) = k1_xboole_0
      | ~ v4_relat_1(B_261,k1_xboole_0)
      | ~ v1_relat_1(B_261) ) ),
    inference(resolution,[status(thm)],[c_2323,c_8])).

tff(c_2359,plain,(
    ! [B_252] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_252)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_252)) ) ),
    inference(resolution,[status(thm)],[c_2306,c_2351])).

tff(c_2369,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2248,c_14,c_14,c_2359])).

tff(c_2307,plain,(
    ! [A_253,B_254] : v4_relat_1(k2_zfmisc_1(A_253,B_254),A_253) ),
    inference(resolution,[status(thm)],[c_6,c_2295])).

tff(c_2310,plain,(
    ! [A_4] : v4_relat_1(k1_xboole_0,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2307])).

tff(c_2374,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | ~ v4_relat_1(k1_xboole_0,A_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2369,c_22])).

tff(c_2384,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2248,c_2310,c_2374])).

tff(c_2705,plain,(
    ! [A_309,B_310,A_311] :
      ( k1_relset_1(A_309,B_310,A_311) = k1_relat_1(A_311)
      | ~ r1_tarski(A_311,k2_zfmisc_1(A_309,B_310)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2463])).

tff(c_2709,plain,(
    ! [A_309,B_310] : k1_relset_1(A_309,B_310,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2384,c_2705])).

tff(c_2725,plain,(
    ! [A_309,B_310] : k1_relset_1(A_309,B_310,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2369,c_2709])).

tff(c_34,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_2514,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_2517,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_2514])).

tff(c_2521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2517])).

tff(c_2523,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_38,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2775,plain,(
    ! [C_319,B_320] :
      ( v1_funct_2(C_319,k1_xboole_0,B_320)
      | k1_relset_1(k1_xboole_0,B_320,C_319) != k1_xboole_0
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_2777,plain,(
    ! [B_320] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_320)
      | k1_relset_1(k1_xboole_0,B_320,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2523,c_2775])).

tff(c_2783,plain,(
    ! [B_320] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2725,c_2777])).

tff(c_4473,plain,(
    ! [B_320] : v1_funct_2('#skF_1','#skF_1',B_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4298,c_4298,c_2783])).

tff(c_4491,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4298,c_4298,c_2369])).

tff(c_4490,plain,(
    ! [A_8] : r1_tarski('#skF_1',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4298,c_2384])).

tff(c_4274,plain,(
    ! [A_374] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_374)
      | m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_3251])).

tff(c_4447,plain,(
    ! [A_429] : ~ r1_tarski(k1_relat_1('#skF_2'),A_429) ),
    inference(splitLeft,[status(thm)],[c_4274])).

tff(c_4459,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_4447])).

tff(c_4460,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4274])).

tff(c_4879,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4298,c_4460])).

tff(c_4883,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_4879,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4886,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4883,c_2])).

tff(c_4889,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4490,c_4886])).

tff(c_4894,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4889,c_4889,c_96])).

tff(c_4898,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4491,c_4894])).

tff(c_5132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4473,c_4898])).

tff(c_5133,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5427,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5412,c_5133])).

tff(c_5444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_48,c_5427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.16  
% 5.93/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.93/2.16  
% 5.93/2.16  %Foreground sorts:
% 5.93/2.16  
% 5.93/2.16  
% 5.93/2.16  %Background operators:
% 5.93/2.16  
% 5.93/2.16  
% 5.93/2.16  %Foreground operators:
% 5.93/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.93/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.93/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.93/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.93/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.93/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.93/2.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.93/2.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.93/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.93/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.93/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.93/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.93/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.16  
% 5.93/2.21  tff(f_104, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.93/2.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.93/2.21  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.93/2.21  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.93/2.21  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.93/2.21  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.93/2.21  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.93/2.21  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.93/2.21  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.93/2.21  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.93/2.21  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.93/2.21  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.93/2.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.93/2.21  tff(c_48, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.93/2.21  tff(c_5412, plain, (![C_503, A_504, B_505]: (m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_505))) | ~r1_tarski(k2_relat_1(C_503), B_505) | ~r1_tarski(k1_relat_1(C_503), A_504) | ~v1_relat_1(C_503))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.93/2.21  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.93/2.21  tff(c_46, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.93/2.21  tff(c_54, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46])).
% 5.93/2.21  tff(c_96, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 5.93/2.21  tff(c_345, plain, (![C_83, A_84, B_85]: (m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~r1_tarski(k2_relat_1(C_83), B_85) | ~r1_tarski(k1_relat_1(C_83), A_84) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.93/2.21  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.93/2.21  tff(c_1428, plain, (![C_189, A_190, B_191]: (r1_tarski(C_189, k2_zfmisc_1(A_190, B_191)) | ~r1_tarski(k2_relat_1(C_189), B_191) | ~r1_tarski(k1_relat_1(C_189), A_190) | ~v1_relat_1(C_189))), inference(resolution, [status(thm)], [c_345, c_16])).
% 5.93/2.21  tff(c_1430, plain, (![A_190]: (r1_tarski('#skF_2', k2_zfmisc_1(A_190, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_190) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_1428])).
% 5.93/2.21  tff(c_1438, plain, (![A_192]: (r1_tarski('#skF_2', k2_zfmisc_1(A_192, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_192))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1430])).
% 5.93/2.21  tff(c_1450, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1438])).
% 5.93/2.21  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.93/2.21  tff(c_257, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.93/2.21  tff(c_268, plain, (![A_74, B_75, A_6]: (k1_relset_1(A_74, B_75, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_74, B_75)))), inference(resolution, [status(thm)], [c_18, c_257])).
% 5.93/2.21  tff(c_1465, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1450, c_268])).
% 5.93/2.21  tff(c_625, plain, (![B_117, C_118, A_119]: (k1_xboole_0=B_117 | v1_funct_2(C_118, A_119, B_117) | k1_relset_1(A_119, B_117, C_118)!=A_119 | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_117))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.93/2.21  tff(c_2110, plain, (![B_228, A_229, A_230]: (k1_xboole_0=B_228 | v1_funct_2(A_229, A_230, B_228) | k1_relset_1(A_230, B_228, A_229)!=A_230 | ~r1_tarski(A_229, k2_zfmisc_1(A_230, B_228)))), inference(resolution, [status(thm)], [c_18, c_625])).
% 5.93/2.21  tff(c_2119, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1450, c_2110])).
% 5.93/2.21  tff(c_2142, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_2119])).
% 5.93/2.21  tff(c_2143, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_96, c_2142])).
% 5.93/2.21  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.93/2.21  tff(c_234, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.93/2.21  tff(c_269, plain, (![A_77, A_78, B_79]: (v4_relat_1(A_77, A_78) | ~r1_tarski(A_77, k2_zfmisc_1(A_78, B_79)))), inference(resolution, [status(thm)], [c_18, c_234])).
% 5.93/2.21  tff(c_286, plain, (![A_80, B_81]: (v4_relat_1(k2_zfmisc_1(A_80, B_81), A_80))), inference(resolution, [status(thm)], [c_6, c_269])).
% 5.93/2.21  tff(c_293, plain, (![A_4]: (v4_relat_1(k1_xboole_0, A_4))), inference(superposition, [status(thm), theory('equality')], [c_12, c_286])).
% 5.93/2.21  tff(c_119, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.93/2.21  tff(c_129, plain, (![C_40]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_119])).
% 5.93/2.21  tff(c_135, plain, (![A_41]: (v1_relat_1(A_41) | ~r1_tarski(A_41, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_129])).
% 5.93/2.21  tff(c_140, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_135])).
% 5.93/2.21  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.93/2.21  tff(c_195, plain, (![B_60, A_61]: (r1_tarski(k1_relat_1(B_60), A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.93/2.21  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.93/2.21  tff(c_222, plain, (![B_60]: (k1_relat_1(B_60)=k1_xboole_0 | ~v4_relat_1(B_60, k1_xboole_0) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_195, c_8])).
% 5.93/2.21  tff(c_290, plain, (![B_81]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_81))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_81)))), inference(resolution, [status(thm)], [c_286, c_222])).
% 5.93/2.21  tff(c_299, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_14, c_14, c_290])).
% 5.93/2.21  tff(c_22, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.93/2.21  tff(c_306, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | ~v4_relat_1(k1_xboole_0, A_8) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_299, c_22])).
% 5.93/2.21  tff(c_318, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | ~v4_relat_1(k1_xboole_0, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_306])).
% 5.93/2.21  tff(c_392, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_318])).
% 5.93/2.21  tff(c_2192, plain, (![A_8]: (r1_tarski('#skF_1', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2143, c_392])).
% 5.93/2.21  tff(c_97, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.93/2.21  tff(c_102, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_97])).
% 5.93/2.21  tff(c_107, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_102])).
% 5.93/2.21  tff(c_2217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2192, c_107])).
% 5.93/2.21  tff(c_2218, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_102])).
% 5.93/2.21  tff(c_2543, plain, (![C_284, A_285, B_286]: (m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~r1_tarski(k2_relat_1(C_284), B_286) | ~r1_tarski(k1_relat_1(C_284), A_285) | ~v1_relat_1(C_284))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.93/2.21  tff(c_3961, plain, (![C_409, A_410, B_411]: (r1_tarski(C_409, k2_zfmisc_1(A_410, B_411)) | ~r1_tarski(k2_relat_1(C_409), B_411) | ~r1_tarski(k1_relat_1(C_409), A_410) | ~v1_relat_1(C_409))), inference(resolution, [status(thm)], [c_2543, c_16])).
% 5.93/2.21  tff(c_3970, plain, (![C_412, A_413]: (r1_tarski(C_412, k2_zfmisc_1(A_413, k2_relat_1(C_412))) | ~r1_tarski(k1_relat_1(C_412), A_413) | ~v1_relat_1(C_412))), inference(resolution, [status(thm)], [c_6, c_3961])).
% 5.93/2.21  tff(c_3997, plain, (![A_413]: (r1_tarski('#skF_2', k2_zfmisc_1(A_413, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_413) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2218, c_3970])).
% 5.93/2.21  tff(c_4037, plain, (![A_415]: (r1_tarski('#skF_2', k2_zfmisc_1(A_415, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_415))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3997])).
% 5.93/2.21  tff(c_4062, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_4037])).
% 5.93/2.21  tff(c_2463, plain, (![A_271, B_272, C_273]: (k1_relset_1(A_271, B_272, C_273)=k1_relat_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.93/2.21  tff(c_2474, plain, (![A_271, B_272, A_6]: (k1_relset_1(A_271, B_272, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_271, B_272)))), inference(resolution, [status(thm)], [c_18, c_2463])).
% 5.93/2.21  tff(c_4099, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4062, c_2474])).
% 5.93/2.21  tff(c_2682, plain, (![B_305, C_306, A_307]: (k1_xboole_0=B_305 | v1_funct_2(C_306, A_307, B_305) | k1_relset_1(A_307, B_305, C_306)!=A_307 | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_307, B_305))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.93/2.21  tff(c_4164, plain, (![B_420, A_421, A_422]: (k1_xboole_0=B_420 | v1_funct_2(A_421, A_422, B_420) | k1_relset_1(A_422, B_420, A_421)!=A_422 | ~r1_tarski(A_421, k2_zfmisc_1(A_422, B_420)))), inference(resolution, [status(thm)], [c_18, c_2682])).
% 5.93/2.21  tff(c_4173, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4062, c_4164])).
% 5.93/2.21  tff(c_4199, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4099, c_4173])).
% 5.93/2.21  tff(c_4200, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_96, c_4199])).
% 5.93/2.21  tff(c_3247, plain, (![C_373, A_374]: (m1_subset_1(C_373, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_373), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_373), A_374) | ~v1_relat_1(C_373))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2543])).
% 5.93/2.21  tff(c_3249, plain, (![A_374]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_374) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2218, c_3247])).
% 5.93/2.21  tff(c_3251, plain, (![A_374]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_374))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3249])).
% 5.93/2.21  tff(c_3252, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3251])).
% 5.93/2.21  tff(c_4229, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4200, c_3252])).
% 5.93/2.21  tff(c_4273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4229])).
% 5.93/2.21  tff(c_4275, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3251])).
% 5.93/2.21  tff(c_4298, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4275, c_8])).
% 5.93/2.21  tff(c_2227, plain, (![C_231, A_232, B_233]: (v1_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.93/2.21  tff(c_2237, plain, (![C_234]: (v1_relat_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2227])).
% 5.93/2.21  tff(c_2243, plain, (![A_235]: (v1_relat_1(A_235) | ~r1_tarski(A_235, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_2237])).
% 5.93/2.21  tff(c_2248, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2243])).
% 5.93/2.21  tff(c_2277, plain, (![C_243, A_244, B_245]: (v4_relat_1(C_243, A_244) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.93/2.21  tff(c_2295, plain, (![A_250, A_251, B_252]: (v4_relat_1(A_250, A_251) | ~r1_tarski(A_250, k2_zfmisc_1(A_251, B_252)))), inference(resolution, [status(thm)], [c_18, c_2277])).
% 5.93/2.21  tff(c_2306, plain, (![A_251, B_252]: (v4_relat_1(k2_zfmisc_1(A_251, B_252), A_251))), inference(resolution, [status(thm)], [c_6, c_2295])).
% 5.93/2.21  tff(c_2323, plain, (![B_259, A_260]: (r1_tarski(k1_relat_1(B_259), A_260) | ~v4_relat_1(B_259, A_260) | ~v1_relat_1(B_259))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.93/2.21  tff(c_2351, plain, (![B_261]: (k1_relat_1(B_261)=k1_xboole_0 | ~v4_relat_1(B_261, k1_xboole_0) | ~v1_relat_1(B_261))), inference(resolution, [status(thm)], [c_2323, c_8])).
% 5.93/2.21  tff(c_2359, plain, (![B_252]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_252))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_252)))), inference(resolution, [status(thm)], [c_2306, c_2351])).
% 5.93/2.21  tff(c_2369, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2248, c_14, c_14, c_2359])).
% 5.93/2.21  tff(c_2307, plain, (![A_253, B_254]: (v4_relat_1(k2_zfmisc_1(A_253, B_254), A_253))), inference(resolution, [status(thm)], [c_6, c_2295])).
% 5.93/2.21  tff(c_2310, plain, (![A_4]: (v4_relat_1(k1_xboole_0, A_4))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2307])).
% 5.93/2.21  tff(c_2374, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | ~v4_relat_1(k1_xboole_0, A_8) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2369, c_22])).
% 5.93/2.21  tff(c_2384, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2248, c_2310, c_2374])).
% 5.93/2.21  tff(c_2705, plain, (![A_309, B_310, A_311]: (k1_relset_1(A_309, B_310, A_311)=k1_relat_1(A_311) | ~r1_tarski(A_311, k2_zfmisc_1(A_309, B_310)))), inference(resolution, [status(thm)], [c_18, c_2463])).
% 5.93/2.21  tff(c_2709, plain, (![A_309, B_310]: (k1_relset_1(A_309, B_310, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2384, c_2705])).
% 5.93/2.21  tff(c_2725, plain, (![A_309, B_310]: (k1_relset_1(A_309, B_310, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2369, c_2709])).
% 5.93/2.21  tff(c_34, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.93/2.21  tff(c_57, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 5.93/2.21  tff(c_2514, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_57])).
% 5.93/2.21  tff(c_2517, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_2514])).
% 5.93/2.21  tff(c_2521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2517])).
% 5.93/2.21  tff(c_2523, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_57])).
% 5.93/2.21  tff(c_38, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.93/2.21  tff(c_2775, plain, (![C_319, B_320]: (v1_funct_2(C_319, k1_xboole_0, B_320) | k1_relset_1(k1_xboole_0, B_320, C_319)!=k1_xboole_0 | ~m1_subset_1(C_319, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 5.93/2.21  tff(c_2777, plain, (![B_320]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_320) | k1_relset_1(k1_xboole_0, B_320, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2523, c_2775])).
% 5.93/2.21  tff(c_2783, plain, (![B_320]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_320))), inference(demodulation, [status(thm), theory('equality')], [c_2725, c_2777])).
% 5.93/2.21  tff(c_4473, plain, (![B_320]: (v1_funct_2('#skF_1', '#skF_1', B_320))), inference(demodulation, [status(thm), theory('equality')], [c_4298, c_4298, c_2783])).
% 5.93/2.21  tff(c_4491, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4298, c_4298, c_2369])).
% 5.93/2.21  tff(c_4490, plain, (![A_8]: (r1_tarski('#skF_1', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4298, c_2384])).
% 5.93/2.21  tff(c_4274, plain, (![A_374]: (~r1_tarski(k1_relat_1('#skF_2'), A_374) | m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_3251])).
% 5.93/2.21  tff(c_4447, plain, (![A_429]: (~r1_tarski(k1_relat_1('#skF_2'), A_429))), inference(splitLeft, [status(thm)], [c_4274])).
% 5.93/2.21  tff(c_4459, plain, $false, inference(resolution, [status(thm)], [c_6, c_4447])).
% 5.93/2.21  tff(c_4460, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_4274])).
% 5.93/2.21  tff(c_4879, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4298, c_4460])).
% 5.93/2.21  tff(c_4883, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_4879, c_16])).
% 5.93/2.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.93/2.21  tff(c_4886, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4883, c_2])).
% 5.93/2.21  tff(c_4889, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4490, c_4886])).
% 5.93/2.21  tff(c_4894, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4889, c_4889, c_96])).
% 5.93/2.21  tff(c_4898, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4491, c_4894])).
% 5.93/2.21  tff(c_5132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4473, c_4898])).
% 5.93/2.21  tff(c_5133, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 5.93/2.21  tff(c_5427, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5412, c_5133])).
% 5.93/2.21  tff(c_5444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_48, c_5427])).
% 5.93/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.21  
% 5.93/2.21  Inference rules
% 5.93/2.21  ----------------------
% 5.93/2.21  #Ref     : 0
% 5.93/2.21  #Sup     : 1131
% 5.93/2.21  #Fact    : 0
% 5.93/2.21  #Define  : 0
% 5.93/2.21  #Split   : 16
% 5.93/2.21  #Chain   : 0
% 5.93/2.21  #Close   : 0
% 5.93/2.21  
% 5.93/2.21  Ordering : KBO
% 5.93/2.21  
% 5.93/2.21  Simplification rules
% 5.93/2.21  ----------------------
% 5.93/2.21  #Subsume      : 160
% 5.93/2.21  #Demod        : 1725
% 5.93/2.21  #Tautology    : 575
% 5.93/2.21  #SimpNegUnit  : 8
% 5.93/2.21  #BackRed      : 227
% 5.93/2.21  
% 5.93/2.21  #Partial instantiations: 0
% 5.93/2.21  #Strategies tried      : 1
% 5.93/2.21  
% 5.93/2.21  Timing (in seconds)
% 5.93/2.21  ----------------------
% 5.93/2.21  Preprocessing        : 0.33
% 5.93/2.21  Parsing              : 0.18
% 5.93/2.21  CNF conversion       : 0.02
% 5.93/2.21  Main loop            : 1.04
% 5.93/2.21  Inferencing          : 0.35
% 5.93/2.21  Reduction            : 0.37
% 5.93/2.21  Demodulation         : 0.27
% 5.93/2.21  BG Simplification    : 0.04
% 5.93/2.21  Subsumption          : 0.20
% 5.93/2.21  Abstraction          : 0.05
% 5.93/2.21  MUC search           : 0.00
% 5.93/2.21  Cooper               : 0.00
% 5.93/2.22  Total                : 1.45
% 5.93/2.22  Index Insertion      : 0.00
% 5.93/2.22  Index Deletion       : 0.00
% 5.93/2.22  Index Matching       : 0.00
% 5.93/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
