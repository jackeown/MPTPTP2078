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
% DateTime   : Thu Dec  3 10:10:45 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 617 expanded)
%              Number of leaves         :   26 ( 212 expanded)
%              Depth                    :   18
%              Number of atoms          :  213 (1493 expanded)
%              Number of equality atoms :   60 ( 487 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3381,plain,(
    ! [A_316] :
      ( r1_tarski(A_316,k2_zfmisc_1(k1_relat_1(A_316),k2_relat_1(A_316)))
      | ~ v1_relat_1(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_710,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1072,plain,(
    ! [A_173,B_174,A_175] :
      ( k1_relset_1(A_173,B_174,A_175) = k1_relat_1(A_175)
      | ~ r1_tarski(A_175,k2_zfmisc_1(A_173,B_174)) ) ),
    inference(resolution,[status(thm)],[c_14,c_710])).

tff(c_1088,plain,(
    ! [A_6] :
      ( k1_relset_1(k1_relat_1(A_6),k2_relat_1(A_6),A_6) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_1072])).

tff(c_1012,plain,(
    ! [B_164,C_165,A_166] :
      ( k1_xboole_0 = B_164
      | v1_funct_2(C_165,A_166,B_164)
      | k1_relset_1(A_166,B_164,C_165) != A_166
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1587,plain,(
    ! [B_219,A_220,A_221] :
      ( k1_xboole_0 = B_219
      | v1_funct_2(A_220,A_221,B_219)
      | k1_relset_1(A_221,B_219,A_220) != A_221
      | ~ r1_tarski(A_220,k2_zfmisc_1(A_221,B_219)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1012])).

tff(c_2968,plain,(
    ! [A_303] :
      ( k2_relat_1(A_303) = k1_xboole_0
      | v1_funct_2(A_303,k1_relat_1(A_303),k2_relat_1(A_303))
      | k1_relset_1(k1_relat_1(A_303),k2_relat_1(A_303),A_303) != k1_relat_1(A_303)
      | ~ v1_relat_1(A_303) ) ),
    inference(resolution,[status(thm)],[c_16,c_1587])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_92,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_2975,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2968,c_92])).

tff(c_2987,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2975])).

tff(c_2990,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2987])).

tff(c_2993,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_2990])).

tff(c_2997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2993])).

tff(c_2998,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2987])).

tff(c_94,plain,(
    ! [C_30,B_31,A_32] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(B_31,A_32)))
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_728,plain,(
    ! [A_130,A_131,B_132] :
      ( v1_xboole_0(A_130)
      | ~ v1_xboole_0(A_131)
      | ~ r1_tarski(A_130,k2_zfmisc_1(B_132,A_131)) ) ),
    inference(resolution,[status(thm)],[c_14,c_94])).

tff(c_738,plain,(
    ! [A_6] :
      ( v1_xboole_0(A_6)
      | ~ v1_xboole_0(k2_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_728])).

tff(c_3010,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2998,c_738])).

tff(c_3021,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2,c_3010])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3028,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3021,c_4])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_179,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k1_relset_1(A_56,B_57,C_58),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_229,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(k1_relset_1(A_65,B_66,C_67),A_65)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(resolution,[status(thm)],[c_179,c_12])).

tff(c_239,plain,(
    ! [B_3,C_67] :
      ( r1_tarski(k1_relset_1(k1_xboole_0,B_3,C_67),k1_xboole_0)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_229])).

tff(c_20,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k1_relset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_45,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_115,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_119,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_115])).

tff(c_285,plain,(
    ! [A_74,B_75,A_76] :
      ( r1_tarski(k1_relset_1(A_74,B_75,A_76),A_74)
      | ~ r1_tarski(A_76,k2_zfmisc_1(A_74,B_75)) ) ),
    inference(resolution,[status(thm)],[c_14,c_229])).

tff(c_101,plain,(
    ! [C_30] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_107,plain,(
    ! [C_30] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_193,plain,(
    ! [B_57,C_58] :
      ( v1_xboole_0(k1_relset_1(k1_xboole_0,B_57,C_58))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_57))) ) ),
    inference(resolution,[status(thm)],[c_179,c_107])).

tff(c_213,plain,(
    ! [B_59,C_60] :
      ( v1_xboole_0(k1_relset_1(k1_xboole_0,B_59,C_60))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_193])).

tff(c_223,plain,(
    ! [B_61,A_62] :
      ( v1_xboole_0(k1_relset_1(k1_xboole_0,B_61,A_62))
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_213])).

tff(c_227,plain,(
    ! [B_61,A_62] :
      ( k1_relset_1(k1_xboole_0,B_61,A_62) = k1_xboole_0
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_223,c_4])).

tff(c_288,plain,(
    ! [B_61,B_75,A_76] :
      ( k1_relset_1(k1_xboole_0,B_61,k1_relset_1(k1_xboole_0,B_75,A_76)) = k1_xboole_0
      | ~ r1_tarski(A_76,k2_zfmisc_1(k1_xboole_0,B_75)) ) ),
    inference(resolution,[status(thm)],[c_285,c_227])).

tff(c_320,plain,(
    ! [B_77,B_78,A_79] :
      ( k1_relset_1(k1_xboole_0,B_77,k1_relset_1(k1_xboole_0,B_78,A_79)) = k1_xboole_0
      | ~ r1_tarski(A_79,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_288])).

tff(c_241,plain,(
    ! [A_65,B_66,A_4] :
      ( r1_tarski(k1_relset_1(A_65,B_66,A_4),A_65)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_14,c_229])).

tff(c_329,plain,(
    ! [B_78,A_79,B_77] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relset_1(k1_xboole_0,B_78,A_79),k2_zfmisc_1(k1_xboole_0,B_77))
      | ~ r1_tarski(A_79,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_241])).

tff(c_350,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relset_1(k1_xboole_0,B_78,A_79),k1_xboole_0)
      | ~ r1_tarski(A_79,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_329])).

tff(c_376,plain,(
    ! [B_83,A_84] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_83,A_84),k1_xboole_0)
      | ~ r1_tarski(A_84,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_350])).

tff(c_408,plain,(
    ! [C_86] :
      ( ~ r1_tarski(C_86,k1_xboole_0)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_239,c_376])).

tff(c_412,plain,(
    ! [B_12,C_13] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_12,C_13),k1_xboole_0)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(resolution,[status(thm)],[c_20,c_408])).

tff(c_444,plain,(
    ! [B_91,C_92] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_91,C_92),k1_xboole_0)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_412])).

tff(c_481,plain,(
    ! [C_96] : ~ m1_subset_1(C_96,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_239,c_444])).

tff(c_492,plain,(
    ! [A_4] : ~ r1_tarski(A_4,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_481])).

tff(c_120,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_159,plain,(
    ! [A_52,B_53,A_54] :
      ( k1_relset_1(A_52,B_53,A_54) = k1_relat_1(A_54)
      | ~ r1_tarski(A_54,k2_zfmisc_1(A_52,B_53)) ) ),
    inference(resolution,[status(thm)],[c_14,c_120])).

tff(c_169,plain,(
    ! [A_6] :
      ( k1_relset_1(k1_relat_1(A_6),k2_relat_1(A_6),A_6) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_159])).

tff(c_358,plain,(
    ! [B_80,C_81,A_82] :
      ( k1_xboole_0 = B_80
      | v1_funct_2(C_81,A_82,B_80)
      | k1_relset_1(A_82,B_80,C_81) != A_82
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_522,plain,(
    ! [B_103,A_104,A_105] :
      ( k1_xboole_0 = B_103
      | v1_funct_2(A_104,A_105,B_103)
      | k1_relset_1(A_105,B_103,A_104) != A_105
      | ~ r1_tarski(A_104,k2_zfmisc_1(A_105,B_103)) ) ),
    inference(resolution,[status(thm)],[c_14,c_358])).

tff(c_638,plain,(
    ! [A_121] :
      ( k2_relat_1(A_121) = k1_xboole_0
      | v1_funct_2(A_121,k1_relat_1(A_121),k2_relat_1(A_121))
      | k1_relset_1(k1_relat_1(A_121),k2_relat_1(A_121),A_121) != k1_relat_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_16,c_522])).

tff(c_641,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_638,c_92])).

tff(c_644,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_641])).

tff(c_645,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_644])).

tff(c_666,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_645])).

tff(c_670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_666])).

tff(c_671,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_686,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_16])).

tff(c_696,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_686])).

tff(c_698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_696])).

tff(c_700,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_749,plain,(
    ! [A_136,C_137] :
      ( k1_relset_1(A_136,k1_xboole_0,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_710])).

tff(c_755,plain,(
    ! [A_136] : k1_relset_1(A_136,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_700,c_749])).

tff(c_769,plain,(
    ! [A_141,B_142,C_143] :
      ( m1_subset_1(k1_relset_1(A_141,B_142,C_143),k1_zfmisc_1(A_141))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_790,plain,(
    ! [A_136] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_136))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_136,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_769])).

tff(c_800,plain,(
    ! [A_144] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_8,c_790])).

tff(c_821,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_800,c_107])).

tff(c_827,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_821,c_4])).

tff(c_799,plain,(
    ! [A_136] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_8,c_790])).

tff(c_861,plain,(
    ! [A_146] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_799])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_868,plain,(
    ! [A_14,B_15] : k1_relset_1(A_14,B_15,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_861,c_22])).

tff(c_883,plain,(
    ! [A_14,B_15] : k1_relset_1(A_14,B_15,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_868])).

tff(c_829,plain,(
    ! [A_136] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_799])).

tff(c_28,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_966,plain,(
    ! [C_157,B_158] :
      ( v1_funct_2(C_157,k1_xboole_0,B_158)
      | k1_relset_1(k1_xboole_0,B_158,C_157) != k1_xboole_0
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_28])).

tff(c_969,plain,(
    ! [B_158] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_158)
      | k1_relset_1(k1_xboole_0,B_158,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_829,c_966])).

tff(c_978,plain,(
    ! [B_158] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_969])).

tff(c_3071,plain,(
    ! [B_158] : v1_funct_2('#skF_1','#skF_1',B_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3028,c_3028,c_978])).

tff(c_3079,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3028,c_3028,c_827])).

tff(c_3000,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2998,c_92])).

tff(c_3160,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3079,c_3028,c_3000])).

tff(c_3374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3071,c_3160])).

tff(c_3375,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_3380,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_3375])).

tff(c_3384,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3381,c_3380])).

tff(c_3388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.92  
% 4.74/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.92  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.74/1.92  
% 4.74/1.92  %Foreground sorts:
% 4.74/1.92  
% 4.74/1.92  
% 4.74/1.92  %Background operators:
% 4.74/1.92  
% 4.74/1.92  
% 4.74/1.92  %Foreground operators:
% 4.74/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.74/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.74/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.74/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.74/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.74/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.74/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.92  
% 5.11/1.95  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.11/1.95  tff(f_44, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 5.11/1.95  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.11/1.95  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.11/1.95  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.11/1.95  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.11/1.95  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.11/1.95  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.11/1.95  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.11/1.95  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.11/1.95  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.11/1.95  tff(c_3381, plain, (![A_316]: (r1_tarski(A_316, k2_zfmisc_1(k1_relat_1(A_316), k2_relat_1(A_316))) | ~v1_relat_1(A_316))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.11/1.95  tff(c_14, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.11/1.95  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.11/1.95  tff(c_16, plain, (![A_6]: (r1_tarski(A_6, k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6))) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.11/1.95  tff(c_710, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.11/1.95  tff(c_1072, plain, (![A_173, B_174, A_175]: (k1_relset_1(A_173, B_174, A_175)=k1_relat_1(A_175) | ~r1_tarski(A_175, k2_zfmisc_1(A_173, B_174)))), inference(resolution, [status(thm)], [c_14, c_710])).
% 5.11/1.95  tff(c_1088, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_1072])).
% 5.11/1.95  tff(c_1012, plain, (![B_164, C_165, A_166]: (k1_xboole_0=B_164 | v1_funct_2(C_165, A_166, B_164) | k1_relset_1(A_166, B_164, C_165)!=A_166 | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_164))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.11/1.95  tff(c_1587, plain, (![B_219, A_220, A_221]: (k1_xboole_0=B_219 | v1_funct_2(A_220, A_221, B_219) | k1_relset_1(A_221, B_219, A_220)!=A_221 | ~r1_tarski(A_220, k2_zfmisc_1(A_221, B_219)))), inference(resolution, [status(thm)], [c_14, c_1012])).
% 5.11/1.95  tff(c_2968, plain, (![A_303]: (k2_relat_1(A_303)=k1_xboole_0 | v1_funct_2(A_303, k1_relat_1(A_303), k2_relat_1(A_303)) | k1_relset_1(k1_relat_1(A_303), k2_relat_1(A_303), A_303)!=k1_relat_1(A_303) | ~v1_relat_1(A_303))), inference(resolution, [status(thm)], [c_16, c_1587])).
% 5.11/1.95  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.11/1.95  tff(c_36, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.11/1.95  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 5.11/1.95  tff(c_92, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_42])).
% 5.11/1.95  tff(c_2975, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2968, c_92])).
% 5.11/1.95  tff(c_2987, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2975])).
% 5.11/1.95  tff(c_2990, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_2987])).
% 5.11/1.95  tff(c_2993, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1088, c_2990])).
% 5.11/1.95  tff(c_2997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2993])).
% 5.11/1.95  tff(c_2998, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2987])).
% 5.11/1.95  tff(c_94, plain, (![C_30, B_31, A_32]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(B_31, A_32))) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.11/1.95  tff(c_728, plain, (![A_130, A_131, B_132]: (v1_xboole_0(A_130) | ~v1_xboole_0(A_131) | ~r1_tarski(A_130, k2_zfmisc_1(B_132, A_131)))), inference(resolution, [status(thm)], [c_14, c_94])).
% 5.11/1.95  tff(c_738, plain, (![A_6]: (v1_xboole_0(A_6) | ~v1_xboole_0(k2_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_728])).
% 5.11/1.95  tff(c_3010, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2998, c_738])).
% 5.11/1.95  tff(c_3021, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2, c_3010])).
% 5.11/1.95  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.11/1.95  tff(c_3028, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3021, c_4])).
% 5.11/1.95  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.11/1.95  tff(c_179, plain, (![A_56, B_57, C_58]: (m1_subset_1(k1_relset_1(A_56, B_57, C_58), k1_zfmisc_1(A_56)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.11/1.95  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.11/1.95  tff(c_229, plain, (![A_65, B_66, C_67]: (r1_tarski(k1_relset_1(A_65, B_66, C_67), A_65) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(resolution, [status(thm)], [c_179, c_12])).
% 5.11/1.95  tff(c_239, plain, (![B_3, C_67]: (r1_tarski(k1_relset_1(k1_xboole_0, B_3, C_67), k1_xboole_0) | ~m1_subset_1(C_67, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_229])).
% 5.11/1.95  tff(c_20, plain, (![A_11, B_12, C_13]: (m1_subset_1(k1_relset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.11/1.95  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.11/1.95  tff(c_24, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.11/1.95  tff(c_45, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 5.11/1.95  tff(c_115, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_45])).
% 5.11/1.95  tff(c_119, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_115])).
% 5.11/1.95  tff(c_285, plain, (![A_74, B_75, A_76]: (r1_tarski(k1_relset_1(A_74, B_75, A_76), A_74) | ~r1_tarski(A_76, k2_zfmisc_1(A_74, B_75)))), inference(resolution, [status(thm)], [c_14, c_229])).
% 5.11/1.95  tff(c_101, plain, (![C_30]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_94])).
% 5.11/1.95  tff(c_107, plain, (![C_30]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_101])).
% 5.11/1.95  tff(c_193, plain, (![B_57, C_58]: (v1_xboole_0(k1_relset_1(k1_xboole_0, B_57, C_58)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_57))))), inference(resolution, [status(thm)], [c_179, c_107])).
% 5.11/1.95  tff(c_213, plain, (![B_59, C_60]: (v1_xboole_0(k1_relset_1(k1_xboole_0, B_59, C_60)) | ~m1_subset_1(C_60, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_193])).
% 5.11/1.95  tff(c_223, plain, (![B_61, A_62]: (v1_xboole_0(k1_relset_1(k1_xboole_0, B_61, A_62)) | ~r1_tarski(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_213])).
% 5.11/1.95  tff(c_227, plain, (![B_61, A_62]: (k1_relset_1(k1_xboole_0, B_61, A_62)=k1_xboole_0 | ~r1_tarski(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_223, c_4])).
% 5.11/1.95  tff(c_288, plain, (![B_61, B_75, A_76]: (k1_relset_1(k1_xboole_0, B_61, k1_relset_1(k1_xboole_0, B_75, A_76))=k1_xboole_0 | ~r1_tarski(A_76, k2_zfmisc_1(k1_xboole_0, B_75)))), inference(resolution, [status(thm)], [c_285, c_227])).
% 5.11/1.95  tff(c_320, plain, (![B_77, B_78, A_79]: (k1_relset_1(k1_xboole_0, B_77, k1_relset_1(k1_xboole_0, B_78, A_79))=k1_xboole_0 | ~r1_tarski(A_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_288])).
% 5.11/1.95  tff(c_241, plain, (![A_65, B_66, A_4]: (r1_tarski(k1_relset_1(A_65, B_66, A_4), A_65) | ~r1_tarski(A_4, k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_14, c_229])).
% 5.11/1.95  tff(c_329, plain, (![B_78, A_79, B_77]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_78, A_79), k2_zfmisc_1(k1_xboole_0, B_77)) | ~r1_tarski(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_320, c_241])).
% 5.11/1.95  tff(c_350, plain, (![B_78, A_79]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_78, A_79), k1_xboole_0) | ~r1_tarski(A_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_329])).
% 5.11/1.95  tff(c_376, plain, (![B_83, A_84]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_83, A_84), k1_xboole_0) | ~r1_tarski(A_84, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_119, c_350])).
% 5.11/1.95  tff(c_408, plain, (![C_86]: (~r1_tarski(C_86, k1_xboole_0) | ~m1_subset_1(C_86, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_239, c_376])).
% 5.11/1.95  tff(c_412, plain, (![B_12, C_13]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_12, C_13), k1_xboole_0) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(resolution, [status(thm)], [c_20, c_408])).
% 5.11/1.95  tff(c_444, plain, (![B_91, C_92]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_91, C_92), k1_xboole_0) | ~m1_subset_1(C_92, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_412])).
% 5.11/1.95  tff(c_481, plain, (![C_96]: (~m1_subset_1(C_96, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_239, c_444])).
% 5.11/1.95  tff(c_492, plain, (![A_4]: (~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_481])).
% 5.11/1.95  tff(c_120, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.11/1.95  tff(c_159, plain, (![A_52, B_53, A_54]: (k1_relset_1(A_52, B_53, A_54)=k1_relat_1(A_54) | ~r1_tarski(A_54, k2_zfmisc_1(A_52, B_53)))), inference(resolution, [status(thm)], [c_14, c_120])).
% 5.11/1.95  tff(c_169, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_159])).
% 5.11/1.95  tff(c_358, plain, (![B_80, C_81, A_82]: (k1_xboole_0=B_80 | v1_funct_2(C_81, A_82, B_80) | k1_relset_1(A_82, B_80, C_81)!=A_82 | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_80))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.11/1.95  tff(c_522, plain, (![B_103, A_104, A_105]: (k1_xboole_0=B_103 | v1_funct_2(A_104, A_105, B_103) | k1_relset_1(A_105, B_103, A_104)!=A_105 | ~r1_tarski(A_104, k2_zfmisc_1(A_105, B_103)))), inference(resolution, [status(thm)], [c_14, c_358])).
% 5.11/1.95  tff(c_638, plain, (![A_121]: (k2_relat_1(A_121)=k1_xboole_0 | v1_funct_2(A_121, k1_relat_1(A_121), k2_relat_1(A_121)) | k1_relset_1(k1_relat_1(A_121), k2_relat_1(A_121), A_121)!=k1_relat_1(A_121) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_16, c_522])).
% 5.11/1.95  tff(c_641, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_638, c_92])).
% 5.11/1.95  tff(c_644, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_641])).
% 5.11/1.95  tff(c_645, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_644])).
% 5.11/1.95  tff(c_666, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_169, c_645])).
% 5.11/1.95  tff(c_670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_666])).
% 5.11/1.95  tff(c_671, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_644])).
% 5.11/1.95  tff(c_686, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_671, c_16])).
% 5.11/1.95  tff(c_696, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_686])).
% 5.11/1.95  tff(c_698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_696])).
% 5.11/1.95  tff(c_700, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_45])).
% 5.11/1.95  tff(c_749, plain, (![A_136, C_137]: (k1_relset_1(A_136, k1_xboole_0, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_710])).
% 5.11/1.95  tff(c_755, plain, (![A_136]: (k1_relset_1(A_136, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_700, c_749])).
% 5.11/1.95  tff(c_769, plain, (![A_141, B_142, C_143]: (m1_subset_1(k1_relset_1(A_141, B_142, C_143), k1_zfmisc_1(A_141)) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.11/1.95  tff(c_790, plain, (![A_136]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_136)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_136, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_755, c_769])).
% 5.11/1.95  tff(c_800, plain, (![A_144]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_144)))), inference(demodulation, [status(thm), theory('equality')], [c_700, c_8, c_790])).
% 5.11/1.95  tff(c_821, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_800, c_107])).
% 5.11/1.95  tff(c_827, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_821, c_4])).
% 5.11/1.95  tff(c_799, plain, (![A_136]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_700, c_8, c_790])).
% 5.11/1.95  tff(c_861, plain, (![A_146]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_146)))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_799])).
% 5.11/1.95  tff(c_22, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.11/1.95  tff(c_868, plain, (![A_14, B_15]: (k1_relset_1(A_14, B_15, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_861, c_22])).
% 5.11/1.95  tff(c_883, plain, (![A_14, B_15]: (k1_relset_1(A_14, B_15, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_827, c_868])).
% 5.11/1.95  tff(c_829, plain, (![A_136]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_799])).
% 5.11/1.95  tff(c_28, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.11/1.95  tff(c_966, plain, (![C_157, B_158]: (v1_funct_2(C_157, k1_xboole_0, B_158) | k1_relset_1(k1_xboole_0, B_158, C_157)!=k1_xboole_0 | ~m1_subset_1(C_157, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_28])).
% 5.11/1.95  tff(c_969, plain, (![B_158]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_158) | k1_relset_1(k1_xboole_0, B_158, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_829, c_966])).
% 5.11/1.95  tff(c_978, plain, (![B_158]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_883, c_969])).
% 5.11/1.95  tff(c_3071, plain, (![B_158]: (v1_funct_2('#skF_1', '#skF_1', B_158))), inference(demodulation, [status(thm), theory('equality')], [c_3028, c_3028, c_978])).
% 5.11/1.95  tff(c_3079, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3028, c_3028, c_827])).
% 5.11/1.95  tff(c_3000, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2998, c_92])).
% 5.11/1.95  tff(c_3160, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3079, c_3028, c_3000])).
% 5.11/1.95  tff(c_3374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3071, c_3160])).
% 5.11/1.95  tff(c_3375, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_42])).
% 5.11/1.95  tff(c_3380, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_3375])).
% 5.11/1.95  tff(c_3384, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3381, c_3380])).
% 5.11/1.95  tff(c_3388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3384])).
% 5.11/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.95  
% 5.11/1.95  Inference rules
% 5.11/1.95  ----------------------
% 5.11/1.95  #Ref     : 0
% 5.11/1.95  #Sup     : 727
% 5.11/1.95  #Fact    : 0
% 5.11/1.95  #Define  : 0
% 5.11/1.95  #Split   : 4
% 5.11/1.95  #Chain   : 0
% 5.11/1.95  #Close   : 0
% 5.11/1.95  
% 5.11/1.95  Ordering : KBO
% 5.11/1.95  
% 5.11/1.95  Simplification rules
% 5.11/1.95  ----------------------
% 5.11/1.95  #Subsume      : 177
% 5.11/1.95  #Demod        : 800
% 5.11/1.95  #Tautology    : 280
% 5.11/1.95  #SimpNegUnit  : 6
% 5.11/1.95  #BackRed      : 68
% 5.11/1.95  
% 5.11/1.95  #Partial instantiations: 0
% 5.11/1.95  #Strategies tried      : 1
% 5.11/1.95  
% 5.11/1.95  Timing (in seconds)
% 5.11/1.95  ----------------------
% 5.11/1.95  Preprocessing        : 0.30
% 5.11/1.95  Parsing              : 0.17
% 5.11/1.95  CNF conversion       : 0.02
% 5.11/1.95  Main loop            : 0.85
% 5.11/1.95  Inferencing          : 0.29
% 5.11/1.95  Reduction            : 0.27
% 5.11/1.95  Demodulation         : 0.20
% 5.11/1.95  BG Simplification    : 0.04
% 5.11/1.95  Subsumption          : 0.18
% 5.11/1.95  Abstraction          : 0.05
% 5.11/1.95  MUC search           : 0.00
% 5.11/1.95  Cooper               : 0.00
% 5.11/1.95  Total                : 1.20
% 5.11/1.95  Index Insertion      : 0.00
% 5.11/1.95  Index Deletion       : 0.00
% 5.11/1.95  Index Matching       : 0.00
% 5.11/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
