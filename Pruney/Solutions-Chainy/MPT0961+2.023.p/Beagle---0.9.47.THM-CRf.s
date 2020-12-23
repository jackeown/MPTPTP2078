%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:44 EST 2020

% Result     : Theorem 4.49s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 648 expanded)
%              Number of leaves         :   26 ( 222 expanded)
%              Depth                    :   18
%              Number of atoms          :  212 (1539 expanded)
%              Number of equality atoms :   60 ( 527 expanded)
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

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3407,plain,(
    ! [A_316] :
      ( r1_tarski(A_316,k2_zfmisc_1(k1_relat_1(A_316),k2_relat_1(A_316)))
      | ~ v1_relat_1(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_705,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1077,plain,(
    ! [A_173,B_174,A_175] :
      ( k1_relset_1(A_173,B_174,A_175) = k1_relat_1(A_175)
      | ~ r1_tarski(A_175,k2_zfmisc_1(A_173,B_174)) ) ),
    inference(resolution,[status(thm)],[c_14,c_705])).

tff(c_1093,plain,(
    ! [A_6] :
      ( k1_relset_1(k1_relat_1(A_6),k2_relat_1(A_6),A_6) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_1077])).

tff(c_1017,plain,(
    ! [B_164,C_165,A_166] :
      ( k1_xboole_0 = B_164
      | v1_funct_2(C_165,A_166,B_164)
      | k1_relset_1(A_166,B_164,C_165) != A_166
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1597,plain,(
    ! [B_219,A_220,A_221] :
      ( k1_xboole_0 = B_219
      | v1_funct_2(A_220,A_221,B_219)
      | k1_relset_1(A_221,B_219,A_220) != A_221
      | ~ r1_tarski(A_220,k2_zfmisc_1(A_221,B_219)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1017])).

tff(c_2986,plain,(
    ! [A_303] :
      ( k2_relat_1(A_303) = k1_xboole_0
      | v1_funct_2(A_303,k1_relat_1(A_303),k2_relat_1(A_303))
      | k1_relset_1(k1_relat_1(A_303),k2_relat_1(A_303),A_303) != k1_relat_1(A_303)
      | ~ v1_relat_1(A_303) ) ),
    inference(resolution,[status(thm)],[c_16,c_1597])).

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

tff(c_2993,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2986,c_92])).

tff(c_3005,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2993])).

tff(c_3008,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3005])).

tff(c_3011,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_3008])).

tff(c_3015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3011])).

tff(c_3016,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3005])).

tff(c_3028,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3016,c_16])).

tff(c_3036,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_3028])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    ! [C_30] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_94])).

tff(c_108,plain,(
    ! [C_33] :
      ( v1_xboole_0(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_113,plain,(
    ! [A_4] :
      ( v1_xboole_0(A_4)
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_3050,plain,(
    v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3036,c_113])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3054,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3050,c_4])).

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

tff(c_107,plain,(
    ! [C_30] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_104])).

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

tff(c_683,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_16])).

tff(c_691,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_683])).

tff(c_693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_691])).

tff(c_695,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_744,plain,(
    ! [A_136,C_137] :
      ( k1_relset_1(A_136,k1_xboole_0,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_705])).

tff(c_750,plain,(
    ! [A_136] : k1_relset_1(A_136,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_695,c_744])).

tff(c_764,plain,(
    ! [A_141,B_142,C_143] :
      ( m1_subset_1(k1_relset_1(A_141,B_142,C_143),k1_zfmisc_1(A_141))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_785,plain,(
    ! [A_136] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_136))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_136,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_764])).

tff(c_795,plain,(
    ! [A_144] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_8,c_785])).

tff(c_816,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_795,c_107])).

tff(c_827,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_816,c_4])).

tff(c_794,plain,(
    ! [A_136] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_8,c_785])).

tff(c_866,plain,(
    ! [A_146] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_794])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_873,plain,(
    ! [A_14,B_15] : k1_relset_1(A_14,B_15,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_866,c_22])).

tff(c_888,plain,(
    ! [A_14,B_15] : k1_relset_1(A_14,B_15,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_873])).

tff(c_829,plain,(
    ! [A_136] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_794])).

tff(c_28,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_971,plain,(
    ! [C_157,B_158] :
      ( v1_funct_2(C_157,k1_xboole_0,B_158)
      | k1_relset_1(k1_xboole_0,B_158,C_157) != k1_xboole_0
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_28])).

tff(c_974,plain,(
    ! [B_158] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_158)
      | k1_relset_1(k1_xboole_0,B_158,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_829,c_971])).

tff(c_983,plain,(
    ! [B_158] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_974])).

tff(c_3123,plain,(
    ! [B_158] : v1_funct_2('#skF_1','#skF_1',B_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3054,c_3054,c_983])).

tff(c_3131,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3054,c_3054,c_827])).

tff(c_3018,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3016,c_92])).

tff(c_3162,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3054,c_3018])).

tff(c_3163,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_3162])).

tff(c_3400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3123,c_3163])).

tff(c_3401,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_3406,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_3401])).

tff(c_3410,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3407,c_3406])).

tff(c_3414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.49/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/1.99  
% 4.83/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/1.99  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.83/1.99  
% 4.83/1.99  %Foreground sorts:
% 4.83/1.99  
% 4.83/1.99  
% 4.83/1.99  %Background operators:
% 4.83/1.99  
% 4.83/1.99  
% 4.83/1.99  %Foreground operators:
% 4.83/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.83/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.83/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.83/1.99  tff('#skF_1', type, '#skF_1': $i).
% 4.83/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.83/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.83/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.83/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.83/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.83/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/1.99  
% 4.83/2.01  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.83/2.01  tff(f_44, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 4.83/2.01  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.83/2.01  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.83/2.01  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.83/2.01  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.83/2.01  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.83/2.01  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.83/2.01  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.83/2.01  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.83/2.01  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.83/2.01  tff(c_3407, plain, (![A_316]: (r1_tarski(A_316, k2_zfmisc_1(k1_relat_1(A_316), k2_relat_1(A_316))) | ~v1_relat_1(A_316))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.83/2.01  tff(c_14, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.83/2.01  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.83/2.01  tff(c_16, plain, (![A_6]: (r1_tarski(A_6, k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6))) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.83/2.01  tff(c_705, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/2.01  tff(c_1077, plain, (![A_173, B_174, A_175]: (k1_relset_1(A_173, B_174, A_175)=k1_relat_1(A_175) | ~r1_tarski(A_175, k2_zfmisc_1(A_173, B_174)))), inference(resolution, [status(thm)], [c_14, c_705])).
% 4.83/2.01  tff(c_1093, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_1077])).
% 4.83/2.01  tff(c_1017, plain, (![B_164, C_165, A_166]: (k1_xboole_0=B_164 | v1_funct_2(C_165, A_166, B_164) | k1_relset_1(A_166, B_164, C_165)!=A_166 | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_164))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.83/2.01  tff(c_1597, plain, (![B_219, A_220, A_221]: (k1_xboole_0=B_219 | v1_funct_2(A_220, A_221, B_219) | k1_relset_1(A_221, B_219, A_220)!=A_221 | ~r1_tarski(A_220, k2_zfmisc_1(A_221, B_219)))), inference(resolution, [status(thm)], [c_14, c_1017])).
% 4.83/2.01  tff(c_2986, plain, (![A_303]: (k2_relat_1(A_303)=k1_xboole_0 | v1_funct_2(A_303, k1_relat_1(A_303), k2_relat_1(A_303)) | k1_relset_1(k1_relat_1(A_303), k2_relat_1(A_303), A_303)!=k1_relat_1(A_303) | ~v1_relat_1(A_303))), inference(resolution, [status(thm)], [c_16, c_1597])).
% 4.83/2.01  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.83/2.01  tff(c_36, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.83/2.01  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 4.83/2.01  tff(c_92, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.83/2.01  tff(c_2993, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2986, c_92])).
% 4.83/2.01  tff(c_3005, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2993])).
% 4.83/2.01  tff(c_3008, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_3005])).
% 4.83/2.01  tff(c_3011, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1093, c_3008])).
% 4.83/2.01  tff(c_3015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3011])).
% 4.83/2.01  tff(c_3016, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3005])).
% 4.83/2.01  tff(c_3028, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3016, c_16])).
% 4.83/2.01  tff(c_3036, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_3028])).
% 4.83/2.01  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.83/2.01  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.83/2.01  tff(c_94, plain, (![C_30, A_31, B_32]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.83/2.01  tff(c_104, plain, (![C_30]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_94])).
% 4.83/2.01  tff(c_108, plain, (![C_33]: (v1_xboole_0(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_104])).
% 4.83/2.01  tff(c_113, plain, (![A_4]: (v1_xboole_0(A_4) | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_108])).
% 4.83/2.01  tff(c_3050, plain, (v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_3036, c_113])).
% 4.83/2.01  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.83/2.01  tff(c_3054, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3050, c_4])).
% 4.83/2.01  tff(c_179, plain, (![A_56, B_57, C_58]: (m1_subset_1(k1_relset_1(A_56, B_57, C_58), k1_zfmisc_1(A_56)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.83/2.01  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.83/2.01  tff(c_229, plain, (![A_65, B_66, C_67]: (r1_tarski(k1_relset_1(A_65, B_66, C_67), A_65) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(resolution, [status(thm)], [c_179, c_12])).
% 4.83/2.01  tff(c_239, plain, (![B_3, C_67]: (r1_tarski(k1_relset_1(k1_xboole_0, B_3, C_67), k1_xboole_0) | ~m1_subset_1(C_67, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_229])).
% 4.83/2.01  tff(c_20, plain, (![A_11, B_12, C_13]: (m1_subset_1(k1_relset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.83/2.01  tff(c_24, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.83/2.01  tff(c_45, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 4.83/2.01  tff(c_115, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_45])).
% 4.83/2.01  tff(c_119, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_115])).
% 4.83/2.01  tff(c_285, plain, (![A_74, B_75, A_76]: (r1_tarski(k1_relset_1(A_74, B_75, A_76), A_74) | ~r1_tarski(A_76, k2_zfmisc_1(A_74, B_75)))), inference(resolution, [status(thm)], [c_14, c_229])).
% 4.83/2.01  tff(c_107, plain, (![C_30]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_104])).
% 4.83/2.01  tff(c_193, plain, (![B_57, C_58]: (v1_xboole_0(k1_relset_1(k1_xboole_0, B_57, C_58)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_57))))), inference(resolution, [status(thm)], [c_179, c_107])).
% 4.83/2.01  tff(c_213, plain, (![B_59, C_60]: (v1_xboole_0(k1_relset_1(k1_xboole_0, B_59, C_60)) | ~m1_subset_1(C_60, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_193])).
% 4.83/2.01  tff(c_223, plain, (![B_61, A_62]: (v1_xboole_0(k1_relset_1(k1_xboole_0, B_61, A_62)) | ~r1_tarski(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_213])).
% 4.83/2.01  tff(c_227, plain, (![B_61, A_62]: (k1_relset_1(k1_xboole_0, B_61, A_62)=k1_xboole_0 | ~r1_tarski(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_223, c_4])).
% 4.83/2.01  tff(c_288, plain, (![B_61, B_75, A_76]: (k1_relset_1(k1_xboole_0, B_61, k1_relset_1(k1_xboole_0, B_75, A_76))=k1_xboole_0 | ~r1_tarski(A_76, k2_zfmisc_1(k1_xboole_0, B_75)))), inference(resolution, [status(thm)], [c_285, c_227])).
% 4.83/2.01  tff(c_320, plain, (![B_77, B_78, A_79]: (k1_relset_1(k1_xboole_0, B_77, k1_relset_1(k1_xboole_0, B_78, A_79))=k1_xboole_0 | ~r1_tarski(A_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_288])).
% 4.83/2.01  tff(c_241, plain, (![A_65, B_66, A_4]: (r1_tarski(k1_relset_1(A_65, B_66, A_4), A_65) | ~r1_tarski(A_4, k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_14, c_229])).
% 4.83/2.01  tff(c_329, plain, (![B_78, A_79, B_77]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_78, A_79), k2_zfmisc_1(k1_xboole_0, B_77)) | ~r1_tarski(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_320, c_241])).
% 4.83/2.01  tff(c_350, plain, (![B_78, A_79]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_78, A_79), k1_xboole_0) | ~r1_tarski(A_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_329])).
% 4.83/2.01  tff(c_376, plain, (![B_83, A_84]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_83, A_84), k1_xboole_0) | ~r1_tarski(A_84, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_119, c_350])).
% 4.83/2.01  tff(c_408, plain, (![C_86]: (~r1_tarski(C_86, k1_xboole_0) | ~m1_subset_1(C_86, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_239, c_376])).
% 4.83/2.01  tff(c_412, plain, (![B_12, C_13]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_12, C_13), k1_xboole_0) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(resolution, [status(thm)], [c_20, c_408])).
% 4.83/2.01  tff(c_444, plain, (![B_91, C_92]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_91, C_92), k1_xboole_0) | ~m1_subset_1(C_92, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_412])).
% 4.83/2.01  tff(c_481, plain, (![C_96]: (~m1_subset_1(C_96, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_239, c_444])).
% 4.83/2.01  tff(c_492, plain, (![A_4]: (~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_481])).
% 4.83/2.01  tff(c_120, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/2.01  tff(c_159, plain, (![A_52, B_53, A_54]: (k1_relset_1(A_52, B_53, A_54)=k1_relat_1(A_54) | ~r1_tarski(A_54, k2_zfmisc_1(A_52, B_53)))), inference(resolution, [status(thm)], [c_14, c_120])).
% 4.83/2.01  tff(c_169, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_159])).
% 4.83/2.01  tff(c_358, plain, (![B_80, C_81, A_82]: (k1_xboole_0=B_80 | v1_funct_2(C_81, A_82, B_80) | k1_relset_1(A_82, B_80, C_81)!=A_82 | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_80))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.83/2.01  tff(c_522, plain, (![B_103, A_104, A_105]: (k1_xboole_0=B_103 | v1_funct_2(A_104, A_105, B_103) | k1_relset_1(A_105, B_103, A_104)!=A_105 | ~r1_tarski(A_104, k2_zfmisc_1(A_105, B_103)))), inference(resolution, [status(thm)], [c_14, c_358])).
% 4.83/2.01  tff(c_638, plain, (![A_121]: (k2_relat_1(A_121)=k1_xboole_0 | v1_funct_2(A_121, k1_relat_1(A_121), k2_relat_1(A_121)) | k1_relset_1(k1_relat_1(A_121), k2_relat_1(A_121), A_121)!=k1_relat_1(A_121) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_16, c_522])).
% 4.83/2.01  tff(c_641, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_638, c_92])).
% 4.83/2.01  tff(c_644, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_641])).
% 4.83/2.01  tff(c_645, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_644])).
% 4.83/2.01  tff(c_666, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_169, c_645])).
% 4.83/2.01  tff(c_670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_666])).
% 4.83/2.01  tff(c_671, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_644])).
% 4.83/2.01  tff(c_683, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_671, c_16])).
% 4.83/2.01  tff(c_691, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_683])).
% 4.83/2.01  tff(c_693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_691])).
% 4.83/2.01  tff(c_695, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_45])).
% 4.83/2.01  tff(c_744, plain, (![A_136, C_137]: (k1_relset_1(A_136, k1_xboole_0, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_705])).
% 4.83/2.01  tff(c_750, plain, (![A_136]: (k1_relset_1(A_136, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_695, c_744])).
% 4.83/2.01  tff(c_764, plain, (![A_141, B_142, C_143]: (m1_subset_1(k1_relset_1(A_141, B_142, C_143), k1_zfmisc_1(A_141)) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.83/2.01  tff(c_785, plain, (![A_136]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_136)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_136, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_750, c_764])).
% 4.83/2.01  tff(c_795, plain, (![A_144]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_144)))), inference(demodulation, [status(thm), theory('equality')], [c_695, c_8, c_785])).
% 4.83/2.01  tff(c_816, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_795, c_107])).
% 4.83/2.01  tff(c_827, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_816, c_4])).
% 4.83/2.01  tff(c_794, plain, (![A_136]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_695, c_8, c_785])).
% 4.83/2.01  tff(c_866, plain, (![A_146]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_146)))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_794])).
% 4.83/2.01  tff(c_22, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/2.01  tff(c_873, plain, (![A_14, B_15]: (k1_relset_1(A_14, B_15, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_866, c_22])).
% 4.83/2.01  tff(c_888, plain, (![A_14, B_15]: (k1_relset_1(A_14, B_15, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_827, c_873])).
% 4.83/2.01  tff(c_829, plain, (![A_136]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_794])).
% 4.83/2.01  tff(c_28, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.83/2.01  tff(c_971, plain, (![C_157, B_158]: (v1_funct_2(C_157, k1_xboole_0, B_158) | k1_relset_1(k1_xboole_0, B_158, C_157)!=k1_xboole_0 | ~m1_subset_1(C_157, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_28])).
% 4.83/2.01  tff(c_974, plain, (![B_158]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_158) | k1_relset_1(k1_xboole_0, B_158, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_829, c_971])).
% 4.83/2.01  tff(c_983, plain, (![B_158]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_974])).
% 4.83/2.01  tff(c_3123, plain, (![B_158]: (v1_funct_2('#skF_1', '#skF_1', B_158))), inference(demodulation, [status(thm), theory('equality')], [c_3054, c_3054, c_983])).
% 4.83/2.01  tff(c_3131, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3054, c_3054, c_827])).
% 4.83/2.01  tff(c_3018, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3016, c_92])).
% 4.83/2.01  tff(c_3162, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3054, c_3018])).
% 4.83/2.01  tff(c_3163, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_3162])).
% 4.83/2.01  tff(c_3400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3123, c_3163])).
% 4.83/2.01  tff(c_3401, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_42])).
% 4.83/2.01  tff(c_3406, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_3401])).
% 4.83/2.01  tff(c_3410, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3407, c_3406])).
% 4.83/2.02  tff(c_3414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3410])).
% 4.83/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.02  
% 4.83/2.02  Inference rules
% 4.83/2.02  ----------------------
% 4.83/2.02  #Ref     : 0
% 4.83/2.02  #Sup     : 734
% 4.83/2.02  #Fact    : 0
% 4.83/2.02  #Define  : 0
% 4.83/2.02  #Split   : 4
% 4.83/2.02  #Chain   : 0
% 4.83/2.02  #Close   : 0
% 4.83/2.02  
% 4.83/2.02  Ordering : KBO
% 4.83/2.02  
% 4.83/2.02  Simplification rules
% 4.83/2.02  ----------------------
% 4.83/2.02  #Subsume      : 180
% 4.83/2.02  #Demod        : 800
% 4.83/2.02  #Tautology    : 279
% 4.83/2.02  #SimpNegUnit  : 6
% 4.83/2.02  #BackRed      : 71
% 4.83/2.02  
% 4.83/2.02  #Partial instantiations: 0
% 4.83/2.02  #Strategies tried      : 1
% 4.83/2.02  
% 4.83/2.02  Timing (in seconds)
% 4.83/2.02  ----------------------
% 4.83/2.02  Preprocessing        : 0.39
% 4.83/2.02  Parsing              : 0.20
% 4.83/2.02  CNF conversion       : 0.02
% 4.83/2.02  Main loop            : 0.78
% 4.83/2.02  Inferencing          : 0.27
% 4.83/2.02  Reduction            : 0.23
% 4.83/2.02  Demodulation         : 0.17
% 4.83/2.02  BG Simplification    : 0.04
% 4.83/2.02  Subsumption          : 0.18
% 4.83/2.02  Abstraction          : 0.05
% 4.83/2.02  MUC search           : 0.00
% 4.83/2.02  Cooper               : 0.00
% 4.83/2.02  Total                : 1.22
% 4.83/2.02  Index Insertion      : 0.00
% 4.83/2.02  Index Deletion       : 0.00
% 4.83/2.02  Index Matching       : 0.00
% 4.83/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
