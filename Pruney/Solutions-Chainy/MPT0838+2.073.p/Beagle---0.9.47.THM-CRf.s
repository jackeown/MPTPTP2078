%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:19 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 276 expanded)
%              Number of leaves         :   44 ( 111 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 556 expanded)
%              Number of equality atoms :   63 ( 128 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_625,plain,(
    ! [A_163,B_164,C_165] :
      ( k1_relset_1(A_163,B_164,C_165) = k1_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_639,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_625])).

tff(c_46,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_641,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_46])).

tff(c_24,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_84,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_90])).

tff(c_302,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_316,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_302])).

tff(c_317,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_46])).

tff(c_112,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_121,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_112])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_339,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_353,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_339])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_214,plain,(
    ! [A_92,C_93,B_94] :
      ( m1_subset_1(A_92,C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_234,plain,(
    ! [A_98,B_99,A_100] :
      ( m1_subset_1(A_98,B_99)
      | ~ r2_hidden(A_98,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_14,c_214])).

tff(c_238,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1('#skF_1'(A_101),B_102)
      | ~ r1_tarski(A_101,B_102)
      | k1_xboole_0 = A_101 ) ),
    inference(resolution,[status(thm)],[c_2,c_234])).

tff(c_68,plain,(
    ! [D_57] :
      ( ~ r2_hidden(D_57,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_57,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_73,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_68])).

tff(c_198,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_262,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_238,c_198])).

tff(c_338,plain,(
    ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_354,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_338])).

tff(c_363,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_354])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_121,c_363])).

tff(c_368,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_370,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_384,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_370])).

tff(c_396,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_384])).

tff(c_128,plain,(
    ! [C_76,A_77,B_78] :
      ( v4_relat_1(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_137,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_128])).

tff(c_156,plain,(
    ! [B_84,A_85] :
      ( k7_relat_1(B_84,A_85) = B_84
      | ~ v4_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_159,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_156])).

tff(c_162,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_159])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_166,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_26])).

tff(c_170,plain,(
    k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_166])).

tff(c_397,plain,(
    k9_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_170])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_222,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(k1_relat_1(B_96),A_97) = k1_relat_1(k7_relat_1(B_96,A_97))
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_508,plain,(
    ! [B_143,A_144] :
      ( k5_xboole_0(k1_relat_1(B_143),k1_relat_1(k7_relat_1(B_143,A_144))) = k4_xboole_0(k1_relat_1(B_143),A_144)
      | ~ v1_relat_1(B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_4])).

tff(c_517,plain,
    ( k5_xboole_0(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) = k4_xboole_0(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_508])).

tff(c_521,plain,(
    k4_xboole_0(k1_relat_1('#skF_4'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_10,c_517])).

tff(c_205,plain,(
    ! [B_90,A_91] :
      ( r1_xboole_0(k1_relat_1(B_90),A_91)
      | k9_relat_1(B_90,A_91) != k1_xboole_0
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_213,plain,(
    ! [B_90,A_91] :
      ( k4_xboole_0(k1_relat_1(B_90),A_91) = k1_relat_1(B_90)
      | k9_relat_1(B_90,A_91) != k1_xboole_0
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_205,c_6])).

tff(c_528,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_4','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_213])).

tff(c_537,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_397,c_528])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_537])).

tff(c_540,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_690,plain,(
    ! [A_179,B_180,C_181] :
      ( k2_relset_1(A_179,B_180,C_181) = k2_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_701,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_690])).

tff(c_705,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_701])).

tff(c_706,plain,(
    k9_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_170])).

tff(c_561,plain,(
    ! [B_148,A_149] :
      ( k3_xboole_0(k1_relat_1(B_148),A_149) = k1_relat_1(k7_relat_1(B_148,A_149))
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_787,plain,(
    ! [B_191,A_192] :
      ( k5_xboole_0(k1_relat_1(B_191),k1_relat_1(k7_relat_1(B_191,A_192))) = k4_xboole_0(k1_relat_1(B_191),A_192)
      | ~ v1_relat_1(B_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_4])).

tff(c_796,plain,
    ( k5_xboole_0(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) = k4_xboole_0(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_787])).

tff(c_800,plain,(
    k4_xboole_0(k1_relat_1('#skF_4'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_10,c_796])).

tff(c_610,plain,(
    ! [B_159,A_160] :
      ( r1_xboole_0(k1_relat_1(B_159),A_160)
      | k9_relat_1(B_159,A_160) != k1_xboole_0
      | ~ v1_relat_1(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_618,plain,(
    ! [B_159,A_160] :
      ( k4_xboole_0(k1_relat_1(B_159),A_160) = k1_relat_1(B_159)
      | k9_relat_1(B_159,A_160) != k1_xboole_0
      | ~ v1_relat_1(B_159) ) ),
    inference(resolution,[status(thm)],[c_610,c_6])).

tff(c_804,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_4','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_618])).

tff(c_814,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_706,c_804])).

tff(c_816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_641,c_814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.41  
% 2.78/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.41  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.78/1.41  
% 2.78/1.41  %Foreground sorts:
% 2.78/1.41  
% 2.78/1.41  
% 2.78/1.41  %Background operators:
% 2.78/1.41  
% 2.78/1.41  
% 2.78/1.41  %Foreground operators:
% 2.78/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.78/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.78/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.41  
% 2.78/1.43  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.78/1.43  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.78/1.43  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.78/1.43  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.78/1.43  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.78/1.43  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.78/1.43  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.78/1.43  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.78/1.43  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.78/1.43  tff(f_51, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.78/1.43  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.78/1.43  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.78/1.43  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.78/1.43  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.78/1.43  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.43  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.78/1.43  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.78/1.43  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.78/1.43  tff(c_625, plain, (![A_163, B_164, C_165]: (k1_relset_1(A_163, B_164, C_165)=k1_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.43  tff(c_639, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_625])).
% 2.78/1.43  tff(c_46, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.78/1.43  tff(c_641, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_639, c_46])).
% 2.78/1.43  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.78/1.43  tff(c_84, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.78/1.43  tff(c_90, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_84])).
% 2.78/1.43  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_90])).
% 2.78/1.43  tff(c_302, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.43  tff(c_316, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_302])).
% 2.78/1.43  tff(c_317, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_316, c_46])).
% 2.78/1.43  tff(c_112, plain, (![C_70, B_71, A_72]: (v5_relat_1(C_70, B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.78/1.43  tff(c_121, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_112])).
% 2.78/1.43  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.78/1.43  tff(c_339, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.43  tff(c_353, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_339])).
% 2.78/1.43  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.43  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.43  tff(c_214, plain, (![A_92, C_93, B_94]: (m1_subset_1(A_92, C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_92, B_94))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.43  tff(c_234, plain, (![A_98, B_99, A_100]: (m1_subset_1(A_98, B_99) | ~r2_hidden(A_98, A_100) | ~r1_tarski(A_100, B_99))), inference(resolution, [status(thm)], [c_14, c_214])).
% 2.78/1.43  tff(c_238, plain, (![A_101, B_102]: (m1_subset_1('#skF_1'(A_101), B_102) | ~r1_tarski(A_101, B_102) | k1_xboole_0=A_101)), inference(resolution, [status(thm)], [c_2, c_234])).
% 2.78/1.43  tff(c_68, plain, (![D_57]: (~r2_hidden(D_57, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_57, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.78/1.43  tff(c_73, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_68])).
% 2.78/1.43  tff(c_198, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_73])).
% 2.78/1.43  tff(c_262, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_238, c_198])).
% 2.78/1.43  tff(c_338, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_262])).
% 2.78/1.43  tff(c_354, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_338])).
% 2.78/1.43  tff(c_363, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_354])).
% 2.78/1.43  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_121, c_363])).
% 2.78/1.43  tff(c_368, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_262])).
% 2.78/1.43  tff(c_370, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.43  tff(c_384, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_370])).
% 2.78/1.43  tff(c_396, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_368, c_384])).
% 2.78/1.43  tff(c_128, plain, (![C_76, A_77, B_78]: (v4_relat_1(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.78/1.43  tff(c_137, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_128])).
% 2.78/1.43  tff(c_156, plain, (![B_84, A_85]: (k7_relat_1(B_84, A_85)=B_84 | ~v4_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.43  tff(c_159, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_137, c_156])).
% 2.78/1.43  tff(c_162, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_159])).
% 2.78/1.43  tff(c_26, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.78/1.43  tff(c_166, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_26])).
% 2.78/1.43  tff(c_170, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_166])).
% 2.78/1.43  tff(c_397, plain, (k9_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_396, c_170])).
% 2.78/1.43  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.43  tff(c_222, plain, (![B_96, A_97]: (k3_xboole_0(k1_relat_1(B_96), A_97)=k1_relat_1(k7_relat_1(B_96, A_97)) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.78/1.43  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.43  tff(c_508, plain, (![B_143, A_144]: (k5_xboole_0(k1_relat_1(B_143), k1_relat_1(k7_relat_1(B_143, A_144)))=k4_xboole_0(k1_relat_1(B_143), A_144) | ~v1_relat_1(B_143))), inference(superposition, [status(thm), theory('equality')], [c_222, c_4])).
% 2.78/1.43  tff(c_517, plain, (k5_xboole_0(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))=k4_xboole_0(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_508])).
% 2.78/1.43  tff(c_521, plain, (k4_xboole_0(k1_relat_1('#skF_4'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_10, c_517])).
% 2.78/1.43  tff(c_205, plain, (![B_90, A_91]: (r1_xboole_0(k1_relat_1(B_90), A_91) | k9_relat_1(B_90, A_91)!=k1_xboole_0 | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.78/1.43  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.43  tff(c_213, plain, (![B_90, A_91]: (k4_xboole_0(k1_relat_1(B_90), A_91)=k1_relat_1(B_90) | k9_relat_1(B_90, A_91)!=k1_xboole_0 | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_205, c_6])).
% 2.78/1.43  tff(c_528, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k9_relat_1('#skF_4', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_521, c_213])).
% 2.78/1.43  tff(c_537, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_397, c_528])).
% 2.78/1.43  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_317, c_537])).
% 2.78/1.43  tff(c_540, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_73])).
% 2.78/1.43  tff(c_690, plain, (![A_179, B_180, C_181]: (k2_relset_1(A_179, B_180, C_181)=k2_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.43  tff(c_701, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_690])).
% 2.78/1.43  tff(c_705, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_540, c_701])).
% 2.78/1.43  tff(c_706, plain, (k9_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_705, c_170])).
% 2.78/1.43  tff(c_561, plain, (![B_148, A_149]: (k3_xboole_0(k1_relat_1(B_148), A_149)=k1_relat_1(k7_relat_1(B_148, A_149)) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.78/1.43  tff(c_787, plain, (![B_191, A_192]: (k5_xboole_0(k1_relat_1(B_191), k1_relat_1(k7_relat_1(B_191, A_192)))=k4_xboole_0(k1_relat_1(B_191), A_192) | ~v1_relat_1(B_191))), inference(superposition, [status(thm), theory('equality')], [c_561, c_4])).
% 2.78/1.43  tff(c_796, plain, (k5_xboole_0(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))=k4_xboole_0(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_787])).
% 2.78/1.43  tff(c_800, plain, (k4_xboole_0(k1_relat_1('#skF_4'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_10, c_796])).
% 2.78/1.43  tff(c_610, plain, (![B_159, A_160]: (r1_xboole_0(k1_relat_1(B_159), A_160) | k9_relat_1(B_159, A_160)!=k1_xboole_0 | ~v1_relat_1(B_159))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.78/1.43  tff(c_618, plain, (![B_159, A_160]: (k4_xboole_0(k1_relat_1(B_159), A_160)=k1_relat_1(B_159) | k9_relat_1(B_159, A_160)!=k1_xboole_0 | ~v1_relat_1(B_159))), inference(resolution, [status(thm)], [c_610, c_6])).
% 2.78/1.43  tff(c_804, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k9_relat_1('#skF_4', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_800, c_618])).
% 2.78/1.43  tff(c_814, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_706, c_804])).
% 2.78/1.43  tff(c_816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_641, c_814])).
% 2.78/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  Inference rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Ref     : 0
% 2.78/1.43  #Sup     : 163
% 2.78/1.43  #Fact    : 0
% 2.78/1.43  #Define  : 0
% 2.78/1.43  #Split   : 4
% 2.78/1.43  #Chain   : 0
% 2.78/1.43  #Close   : 0
% 2.78/1.43  
% 2.78/1.43  Ordering : KBO
% 2.78/1.43  
% 2.78/1.43  Simplification rules
% 2.78/1.43  ----------------------
% 2.78/1.43  #Subsume      : 15
% 2.78/1.43  #Demod        : 58
% 2.78/1.43  #Tautology    : 61
% 2.78/1.43  #SimpNegUnit  : 2
% 2.78/1.43  #BackRed      : 10
% 2.78/1.43  
% 2.78/1.43  #Partial instantiations: 0
% 2.78/1.43  #Strategies tried      : 1
% 2.78/1.43  
% 2.78/1.43  Timing (in seconds)
% 2.78/1.43  ----------------------
% 2.78/1.44  Preprocessing        : 0.32
% 2.78/1.44  Parsing              : 0.17
% 2.78/1.44  CNF conversion       : 0.02
% 2.78/1.44  Main loop            : 0.34
% 2.78/1.44  Inferencing          : 0.14
% 2.78/1.44  Reduction            : 0.10
% 2.78/1.44  Demodulation         : 0.06
% 2.78/1.44  BG Simplification    : 0.02
% 2.78/1.44  Subsumption          : 0.05
% 2.78/1.44  Abstraction          : 0.02
% 2.78/1.44  MUC search           : 0.00
% 2.78/1.44  Cooper               : 0.00
% 2.78/1.44  Total                : 0.70
% 2.78/1.44  Index Insertion      : 0.00
% 2.78/1.44  Index Deletion       : 0.00
% 2.78/1.44  Index Matching       : 0.00
% 2.78/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
