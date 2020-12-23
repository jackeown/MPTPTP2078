%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:14 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 284 expanded)
%              Number of leaves         :   41 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 596 expanded)
%              Number of equality atoms :   64 ( 126 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
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

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1175,plain,(
    ! [A_204,B_205,C_206] :
      ( k1_relset_1(A_204,B_205,C_206) = k1_relat_1(C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1199,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_1175])).

tff(c_46,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1200,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_46])).

tff(c_24,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_69,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_69])).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_76])).

tff(c_427,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_451,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_427])).

tff(c_452,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_46])).

tff(c_168,plain,(
    ! [C_83,B_84,A_85] :
      ( v5_relat_1(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_182,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_168])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_366,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_390,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_366])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_146,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_2'(A_87),B_88)
      | ~ r1_tarski(A_87,B_88)
      | k1_xboole_0 = A_87 ) ),
    inference(resolution,[status(thm)],[c_8,c_146])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_217,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1('#skF_2'(A_90),B_91)
      | ~ r1_tarski(A_90,B_91)
      | k1_xboole_0 = A_90 ) ),
    inference(resolution,[status(thm)],[c_203,c_16])).

tff(c_63,plain,(
    ! [D_57] :
      ( ~ r2_hidden(D_57,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_57,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_130,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_235,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_217,c_130])).

tff(c_323,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_391,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_323])).

tff(c_402,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_391])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_182,c_402])).

tff(c_407,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_565,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_584,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_565])).

tff(c_590,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_584])).

tff(c_153,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_167,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_153])).

tff(c_32,plain,(
    ! [B_26,A_25] :
      ( k7_relat_1(B_26,A_25) = B_26
      | ~ v4_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_185,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_167,c_32])).

tff(c_188,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_185])).

tff(c_34,plain,(
    ! [B_28,A_27] :
      ( k3_xboole_0(k1_relat_1(B_28),A_27) = k1_relat_1(k7_relat_1(B_28,A_27))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_246,plain,(
    ! [B_94,A_95] :
      ( k7_relat_1(B_94,k3_xboole_0(k1_relat_1(B_94),A_95)) = k7_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_713,plain,(
    ! [B_150,A_151] :
      ( k7_relat_1(B_150,k1_relat_1(k7_relat_1(B_150,A_151))) = k7_relat_1(B_150,A_151)
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_246])).

tff(c_734,plain,
    ( k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = k7_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_713])).

tff(c_740,plain,(
    k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_188,c_734])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_759,plain,
    ( k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_26])).

tff(c_765,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_590,c_759])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_518,plain,(
    ! [B_124,A_125] :
      ( k9_relat_1(B_124,A_125) != k1_xboole_0
      | ~ r1_tarski(A_125,k1_relat_1(B_124))
      | k1_xboole_0 = A_125
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_534,plain,(
    ! [B_124] :
      ( k9_relat_1(B_124,k1_relat_1(B_124)) != k1_xboole_0
      | k1_relat_1(B_124) = k1_xboole_0
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_14,c_518])).

tff(c_770,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_534])).

tff(c_775,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_770])).

tff(c_777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_775])).

tff(c_778,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1007,plain,(
    ! [A_189,B_190,C_191] :
      ( k2_relset_1(A_189,B_190,C_191) = k2_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1026,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_1007])).

tff(c_1032,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_1026])).

tff(c_814,plain,(
    ! [C_159,A_160,B_161] :
      ( v4_relat_1(C_159,A_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_828,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_814])).

tff(c_838,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_828,c_32])).

tff(c_841,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_838])).

tff(c_941,plain,(
    ! [B_177,A_178] :
      ( k7_relat_1(B_177,k3_xboole_0(k1_relat_1(B_177),A_178)) = k7_relat_1(B_177,A_178)
      | ~ v1_relat_1(B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1285,plain,(
    ! [B_222,A_223] :
      ( k7_relat_1(B_222,k1_relat_1(k7_relat_1(B_222,A_223))) = k7_relat_1(B_222,A_223)
      | ~ v1_relat_1(B_222)
      | ~ v1_relat_1(B_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_941])).

tff(c_1306,plain,
    ( k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = k7_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_1285])).

tff(c_1312,plain,(
    k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_841,c_1306])).

tff(c_1319,plain,
    ( k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1312,c_26])).

tff(c_1325,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1032,c_1319])).

tff(c_1109,plain,(
    ! [B_195,A_196] :
      ( k9_relat_1(B_195,A_196) != k1_xboole_0
      | ~ r1_tarski(A_196,k1_relat_1(B_195))
      | k1_xboole_0 = A_196
      | ~ v1_relat_1(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1125,plain,(
    ! [B_195] :
      ( k9_relat_1(B_195,k1_relat_1(B_195)) != k1_xboole_0
      | k1_relat_1(B_195) = k1_xboole_0
      | ~ v1_relat_1(B_195) ) ),
    inference(resolution,[status(thm)],[c_14,c_1109])).

tff(c_1330,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_1125])).

tff(c_1335,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1330])).

tff(c_1337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1200,c_1335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.58  
% 3.47/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.59  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.47/1.59  
% 3.47/1.59  %Foreground sorts:
% 3.47/1.59  
% 3.47/1.59  
% 3.47/1.59  %Background operators:
% 3.47/1.59  
% 3.47/1.59  
% 3.47/1.59  %Foreground operators:
% 3.47/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.47/1.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.47/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.47/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.47/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.47/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.47/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.59  
% 3.47/1.61  tff(f_128, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.47/1.61  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.47/1.61  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.47/1.61  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.47/1.61  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.47/1.61  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.47/1.61  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.47/1.61  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.47/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.47/1.61  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.47/1.61  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.47/1.61  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.47/1.61  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 3.47/1.61  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.47/1.61  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.47/1.61  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 3.47/1.61  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.47/1.61  tff(c_1175, plain, (![A_204, B_205, C_206]: (k1_relset_1(A_204, B_205, C_206)=k1_relat_1(C_206) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.47/1.61  tff(c_1199, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_1175])).
% 3.47/1.61  tff(c_46, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.47/1.61  tff(c_1200, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_46])).
% 3.47/1.61  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.47/1.61  tff(c_69, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.47/1.61  tff(c_76, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_69])).
% 3.47/1.61  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_76])).
% 3.47/1.61  tff(c_427, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.47/1.61  tff(c_451, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_427])).
% 3.47/1.61  tff(c_452, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_451, c_46])).
% 3.47/1.61  tff(c_168, plain, (![C_83, B_84, A_85]: (v5_relat_1(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.61  tff(c_182, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_168])).
% 3.47/1.61  tff(c_22, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.47/1.61  tff(c_366, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.61  tff(c_390, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_366])).
% 3.47/1.61  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.47/1.61  tff(c_146, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.61  tff(c_203, plain, (![A_87, B_88]: (r2_hidden('#skF_2'(A_87), B_88) | ~r1_tarski(A_87, B_88) | k1_xboole_0=A_87)), inference(resolution, [status(thm)], [c_8, c_146])).
% 3.47/1.61  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.61  tff(c_217, plain, (![A_90, B_91]: (m1_subset_1('#skF_2'(A_90), B_91) | ~r1_tarski(A_90, B_91) | k1_xboole_0=A_90)), inference(resolution, [status(thm)], [c_203, c_16])).
% 3.47/1.61  tff(c_63, plain, (![D_57]: (~r2_hidden(D_57, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_57, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.47/1.61  tff(c_68, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_63])).
% 3.47/1.61  tff(c_130, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.47/1.61  tff(c_235, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_217, c_130])).
% 3.47/1.61  tff(c_323, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_235])).
% 3.47/1.61  tff(c_391, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_323])).
% 3.47/1.61  tff(c_402, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_391])).
% 3.47/1.61  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_182, c_402])).
% 3.47/1.61  tff(c_407, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_235])).
% 3.47/1.61  tff(c_565, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.61  tff(c_584, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_565])).
% 3.47/1.61  tff(c_590, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_407, c_584])).
% 3.47/1.61  tff(c_153, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.61  tff(c_167, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_153])).
% 3.47/1.61  tff(c_32, plain, (![B_26, A_25]: (k7_relat_1(B_26, A_25)=B_26 | ~v4_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.47/1.61  tff(c_185, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_167, c_32])).
% 3.47/1.61  tff(c_188, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_185])).
% 3.47/1.61  tff(c_34, plain, (![B_28, A_27]: (k3_xboole_0(k1_relat_1(B_28), A_27)=k1_relat_1(k7_relat_1(B_28, A_27)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.61  tff(c_246, plain, (![B_94, A_95]: (k7_relat_1(B_94, k3_xboole_0(k1_relat_1(B_94), A_95))=k7_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.47/1.61  tff(c_713, plain, (![B_150, A_151]: (k7_relat_1(B_150, k1_relat_1(k7_relat_1(B_150, A_151)))=k7_relat_1(B_150, A_151) | ~v1_relat_1(B_150) | ~v1_relat_1(B_150))), inference(superposition, [status(thm), theory('equality')], [c_34, c_246])).
% 3.47/1.61  tff(c_734, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))=k7_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_188, c_713])).
% 3.47/1.61  tff(c_740, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_188, c_734])).
% 3.47/1.61  tff(c_26, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.47/1.61  tff(c_759, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_740, c_26])).
% 3.47/1.61  tff(c_765, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_590, c_759])).
% 3.47/1.61  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.47/1.61  tff(c_518, plain, (![B_124, A_125]: (k9_relat_1(B_124, A_125)!=k1_xboole_0 | ~r1_tarski(A_125, k1_relat_1(B_124)) | k1_xboole_0=A_125 | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.47/1.61  tff(c_534, plain, (![B_124]: (k9_relat_1(B_124, k1_relat_1(B_124))!=k1_xboole_0 | k1_relat_1(B_124)=k1_xboole_0 | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_14, c_518])).
% 3.47/1.61  tff(c_770, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_765, c_534])).
% 3.47/1.61  tff(c_775, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_770])).
% 3.47/1.61  tff(c_777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_452, c_775])).
% 3.47/1.61  tff(c_778, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 3.47/1.61  tff(c_1007, plain, (![A_189, B_190, C_191]: (k2_relset_1(A_189, B_190, C_191)=k2_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.47/1.61  tff(c_1026, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_1007])).
% 3.47/1.61  tff(c_1032, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_778, c_1026])).
% 3.47/1.61  tff(c_814, plain, (![C_159, A_160, B_161]: (v4_relat_1(C_159, A_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.61  tff(c_828, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_814])).
% 3.47/1.61  tff(c_838, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_828, c_32])).
% 3.47/1.61  tff(c_841, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_838])).
% 3.47/1.61  tff(c_941, plain, (![B_177, A_178]: (k7_relat_1(B_177, k3_xboole_0(k1_relat_1(B_177), A_178))=k7_relat_1(B_177, A_178) | ~v1_relat_1(B_177))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.47/1.61  tff(c_1285, plain, (![B_222, A_223]: (k7_relat_1(B_222, k1_relat_1(k7_relat_1(B_222, A_223)))=k7_relat_1(B_222, A_223) | ~v1_relat_1(B_222) | ~v1_relat_1(B_222))), inference(superposition, [status(thm), theory('equality')], [c_34, c_941])).
% 3.47/1.61  tff(c_1306, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))=k7_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_841, c_1285])).
% 3.47/1.61  tff(c_1312, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_841, c_1306])).
% 3.47/1.61  tff(c_1319, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1312, c_26])).
% 3.47/1.61  tff(c_1325, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1032, c_1319])).
% 3.47/1.61  tff(c_1109, plain, (![B_195, A_196]: (k9_relat_1(B_195, A_196)!=k1_xboole_0 | ~r1_tarski(A_196, k1_relat_1(B_195)) | k1_xboole_0=A_196 | ~v1_relat_1(B_195))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.47/1.61  tff(c_1125, plain, (![B_195]: (k9_relat_1(B_195, k1_relat_1(B_195))!=k1_xboole_0 | k1_relat_1(B_195)=k1_xboole_0 | ~v1_relat_1(B_195))), inference(resolution, [status(thm)], [c_14, c_1109])).
% 3.47/1.61  tff(c_1330, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1325, c_1125])).
% 3.47/1.61  tff(c_1335, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1330])).
% 3.47/1.61  tff(c_1337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1200, c_1335])).
% 3.47/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.61  
% 3.47/1.61  Inference rules
% 3.47/1.61  ----------------------
% 3.47/1.61  #Ref     : 0
% 3.47/1.61  #Sup     : 265
% 3.47/1.61  #Fact    : 0
% 3.47/1.61  #Define  : 0
% 3.47/1.61  #Split   : 5
% 3.47/1.61  #Chain   : 0
% 3.47/1.61  #Close   : 0
% 3.47/1.61  
% 3.47/1.61  Ordering : KBO
% 3.47/1.61  
% 3.47/1.61  Simplification rules
% 3.47/1.61  ----------------------
% 3.47/1.61  #Subsume      : 25
% 3.47/1.61  #Demod        : 100
% 3.47/1.61  #Tautology    : 102
% 3.47/1.61  #SimpNegUnit  : 3
% 3.47/1.61  #BackRed      : 15
% 3.47/1.61  
% 3.47/1.61  #Partial instantiations: 0
% 3.47/1.61  #Strategies tried      : 1
% 3.47/1.61  
% 3.47/1.61  Timing (in seconds)
% 3.47/1.61  ----------------------
% 3.47/1.61  Preprocessing        : 0.33
% 3.47/1.61  Parsing              : 0.18
% 3.47/1.61  CNF conversion       : 0.02
% 3.47/1.61  Main loop            : 0.44
% 3.47/1.61  Inferencing          : 0.17
% 3.47/1.61  Reduction            : 0.12
% 3.47/1.61  Demodulation         : 0.08
% 3.47/1.61  BG Simplification    : 0.02
% 3.47/1.61  Subsumption          : 0.08
% 3.47/1.61  Abstraction          : 0.02
% 3.47/1.61  MUC search           : 0.00
% 3.47/1.61  Cooper               : 0.00
% 3.47/1.61  Total                : 0.81
% 3.47/1.61  Index Insertion      : 0.00
% 3.47/1.61  Index Deletion       : 0.00
% 3.47/1.61  Index Matching       : 0.00
% 3.47/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
