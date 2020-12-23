%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:17 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 258 expanded)
%              Number of leaves         :   39 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 557 expanded)
%              Number of equality atoms :   38 ( 119 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_119,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_22,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_144,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_147,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_144])).

tff(c_154,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_147])).

tff(c_24,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_162,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_154,c_24])).

tff(c_174,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1('#skF_2'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_275,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_262])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_219,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_308,plain,(
    ! [A_105,B_106,B_107] :
      ( r2_hidden('#skF_1'(A_105,B_106),B_107)
      | ~ r1_tarski(A_105,B_107)
      | r1_tarski(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_6,c_219])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_424,plain,(
    ! [A_124,B_125,B_126] :
      ( m1_subset_1('#skF_1'(A_124,B_125),B_126)
      | ~ r1_tarski(A_124,B_126)
      | r1_tarski(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_308,c_12])).

tff(c_330,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_343,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_330])).

tff(c_204,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_47,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_217,plain,(
    ! [B_73] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_73),'#skF_5')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_73) ) ),
    inference(resolution,[status(thm)],[c_204,c_44])).

tff(c_347,plain,(
    ! [B_73] :
      ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_6'),B_73),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_343,c_217])).

tff(c_461,plain,(
    ! [B_125] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
      | r1_tarski(k2_relat_1('#skF_6'),B_125) ) ),
    inference(resolution,[status(thm)],[c_424,c_347])).

tff(c_469,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_472,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_469])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_275,c_472])).

tff(c_489,plain,(
    ! [B_129] : r1_tarski(k2_relat_1('#skF_6'),B_129) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_225,plain,(
    ! [A_11,B_75,B_12] :
      ( r2_hidden(A_11,B_75)
      | ~ r1_tarski(B_12,B_75)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_219])).

tff(c_495,plain,(
    ! [A_11,B_129] :
      ( r2_hidden(A_11,B_129)
      | v1_xboole_0(k2_relat_1('#skF_6'))
      | ~ m1_subset_1(A_11,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_489,c_225])).

tff(c_519,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_495])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_522,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_519,c_8])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_522])).

tff(c_529,plain,(
    ! [A_133,B_134] :
      ( r2_hidden(A_133,B_134)
      | ~ m1_subset_1(A_133,k2_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_495])).

tff(c_543,plain,(
    ! [B_135] : r2_hidden('#skF_2'(k2_relat_1('#skF_6')),B_135) ),
    inference(resolution,[status(thm)],[c_10,c_529])).

tff(c_560,plain,(
    ! [B_135] : m1_subset_1('#skF_2'(k2_relat_1('#skF_6')),B_135) ),
    inference(resolution,[status(thm)],[c_543,c_12])).

tff(c_164,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(A_65,B_66)
      | v1_xboole_0(B_66)
      | ~ m1_subset_1(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    ! [A_65] :
      ( ~ m1_subset_1(A_65,'#skF_5')
      | v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(A_65,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_164,c_44])).

tff(c_279,plain,(
    ! [A_98] :
      ( ~ m1_subset_1(A_98,'#skF_5')
      | ~ m1_subset_1(A_98,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_289,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_279])).

tff(c_345,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_289])).

tff(c_572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_345])).

tff(c_573,plain,(
    v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_577,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_573,c_8])).

tff(c_736,plain,(
    ! [A_179,B_180,C_181] :
      ( k2_relset_1(A_179,B_180,C_181) = k2_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_743,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_736])).

tff(c_750,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_743])).

tff(c_752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_750])).

tff(c_753,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_46,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_762,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_46])).

tff(c_30,plain,(
    ! [A_21] : k1_relat_1('#skF_3'(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [A_21] : v1_relat_1('#skF_3'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,(
    ! [A_57] :
      ( k1_relat_1(A_57) != k1_xboole_0
      | k1_xboole_0 = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_74,plain,(
    ! [A_21] :
      ( k1_relat_1('#skF_3'(A_21)) != k1_xboole_0
      | '#skF_3'(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_68])).

tff(c_79,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | '#skF_3'(A_58) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_74])).

tff(c_85,plain,(
    ! [A_58] :
      ( k1_relat_1(k1_xboole_0) = A_58
      | k1_xboole_0 != A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_30])).

tff(c_795,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_753,c_85])).

tff(c_996,plain,(
    ! [A_224,B_225,C_226] :
      ( k1_relset_1(A_224,B_225,C_226) = k1_relat_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1003,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_996])).

tff(c_1010,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_1003])).

tff(c_1012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_1010])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:46:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.52  
% 3.44/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.52  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.44/1.52  
% 3.44/1.52  %Foreground sorts:
% 3.44/1.52  
% 3.44/1.52  
% 3.44/1.52  %Background operators:
% 3.44/1.52  
% 3.44/1.52  
% 3.44/1.52  %Foreground operators:
% 3.44/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.44/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.52  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.44/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.44/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.44/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.52  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.44/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.52  
% 3.44/1.54  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.44/1.54  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.44/1.54  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.44/1.54  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.44/1.54  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.44/1.54  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.44/1.54  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.44/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.44/1.54  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.44/1.54  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.44/1.54  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.44/1.54  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.44/1.54  tff(f_84, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 3.44/1.54  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.44/1.54  tff(c_22, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.44/1.54  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.44/1.54  tff(c_144, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.54  tff(c_147, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_144])).
% 3.44/1.54  tff(c_154, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_147])).
% 3.44/1.54  tff(c_24, plain, (![A_20]: (k2_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.44/1.54  tff(c_162, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_154, c_24])).
% 3.44/1.54  tff(c_174, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_162])).
% 3.44/1.54  tff(c_10, plain, (![A_7]: (m1_subset_1('#skF_2'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.54  tff(c_262, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.44/1.54  tff(c_275, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_262])).
% 3.44/1.54  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.44/1.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.54  tff(c_219, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.54  tff(c_308, plain, (![A_105, B_106, B_107]: (r2_hidden('#skF_1'(A_105, B_106), B_107) | ~r1_tarski(A_105, B_107) | r1_tarski(A_105, B_106))), inference(resolution, [status(thm)], [c_6, c_219])).
% 3.44/1.54  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.54  tff(c_424, plain, (![A_124, B_125, B_126]: (m1_subset_1('#skF_1'(A_124, B_125), B_126) | ~r1_tarski(A_124, B_126) | r1_tarski(A_124, B_125))), inference(resolution, [status(thm)], [c_308, c_12])).
% 3.44/1.54  tff(c_330, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.44/1.54  tff(c_343, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_330])).
% 3.44/1.54  tff(c_204, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.54  tff(c_44, plain, (![D_47]: (~r2_hidden(D_47, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_47, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.44/1.54  tff(c_217, plain, (![B_73]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_73), '#skF_5') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_73))), inference(resolution, [status(thm)], [c_204, c_44])).
% 3.44/1.54  tff(c_347, plain, (![B_73]: (~m1_subset_1('#skF_1'(k2_relat_1('#skF_6'), B_73), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_73))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_343, c_217])).
% 3.44/1.54  tff(c_461, plain, (![B_125]: (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | r1_tarski(k2_relat_1('#skF_6'), B_125))), inference(resolution, [status(thm)], [c_424, c_347])).
% 3.44/1.54  tff(c_469, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_461])).
% 3.44/1.54  tff(c_472, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_469])).
% 3.44/1.54  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_275, c_472])).
% 3.44/1.54  tff(c_489, plain, (![B_129]: (r1_tarski(k2_relat_1('#skF_6'), B_129))), inference(splitRight, [status(thm)], [c_461])).
% 3.44/1.54  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.54  tff(c_225, plain, (![A_11, B_75, B_12]: (r2_hidden(A_11, B_75) | ~r1_tarski(B_12, B_75) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_219])).
% 3.44/1.54  tff(c_495, plain, (![A_11, B_129]: (r2_hidden(A_11, B_129) | v1_xboole_0(k2_relat_1('#skF_6')) | ~m1_subset_1(A_11, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_489, c_225])).
% 3.44/1.54  tff(c_519, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_495])).
% 3.44/1.54  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.54  tff(c_522, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_519, c_8])).
% 3.44/1.54  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_522])).
% 3.44/1.54  tff(c_529, plain, (![A_133, B_134]: (r2_hidden(A_133, B_134) | ~m1_subset_1(A_133, k2_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_495])).
% 3.44/1.54  tff(c_543, plain, (![B_135]: (r2_hidden('#skF_2'(k2_relat_1('#skF_6')), B_135))), inference(resolution, [status(thm)], [c_10, c_529])).
% 3.44/1.54  tff(c_560, plain, (![B_135]: (m1_subset_1('#skF_2'(k2_relat_1('#skF_6')), B_135))), inference(resolution, [status(thm)], [c_543, c_12])).
% 3.44/1.54  tff(c_164, plain, (![A_65, B_66]: (r2_hidden(A_65, B_66) | v1_xboole_0(B_66) | ~m1_subset_1(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.54  tff(c_172, plain, (![A_65]: (~m1_subset_1(A_65, '#skF_5') | v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(A_65, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_164, c_44])).
% 3.44/1.54  tff(c_279, plain, (![A_98]: (~m1_subset_1(A_98, '#skF_5') | ~m1_subset_1(A_98, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_172])).
% 3.44/1.54  tff(c_289, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_10, c_279])).
% 3.44/1.54  tff(c_345, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_289])).
% 3.44/1.54  tff(c_572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_345])).
% 3.44/1.54  tff(c_573, plain, (v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_172])).
% 3.44/1.54  tff(c_577, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_573, c_8])).
% 3.44/1.54  tff(c_736, plain, (![A_179, B_180, C_181]: (k2_relset_1(A_179, B_180, C_181)=k2_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.44/1.54  tff(c_743, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_736])).
% 3.44/1.54  tff(c_750, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_577, c_743])).
% 3.44/1.54  tff(c_752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_750])).
% 3.44/1.54  tff(c_753, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_162])).
% 3.44/1.54  tff(c_46, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.44/1.54  tff(c_762, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_46])).
% 3.44/1.54  tff(c_30, plain, (![A_21]: (k1_relat_1('#skF_3'(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.54  tff(c_34, plain, (![A_21]: (v1_relat_1('#skF_3'(A_21)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.54  tff(c_68, plain, (![A_57]: (k1_relat_1(A_57)!=k1_xboole_0 | k1_xboole_0=A_57 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.44/1.54  tff(c_74, plain, (![A_21]: (k1_relat_1('#skF_3'(A_21))!=k1_xboole_0 | '#skF_3'(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_68])).
% 3.44/1.54  tff(c_79, plain, (![A_58]: (k1_xboole_0!=A_58 | '#skF_3'(A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_74])).
% 3.44/1.54  tff(c_85, plain, (![A_58]: (k1_relat_1(k1_xboole_0)=A_58 | k1_xboole_0!=A_58)), inference(superposition, [status(thm), theory('equality')], [c_79, c_30])).
% 3.44/1.54  tff(c_795, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_753, c_85])).
% 3.44/1.54  tff(c_996, plain, (![A_224, B_225, C_226]: (k1_relset_1(A_224, B_225, C_226)=k1_relat_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.44/1.54  tff(c_1003, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_996])).
% 3.44/1.54  tff(c_1010, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_795, c_1003])).
% 3.44/1.54  tff(c_1012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_762, c_1010])).
% 3.44/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.54  
% 3.44/1.54  Inference rules
% 3.44/1.54  ----------------------
% 3.44/1.54  #Ref     : 4
% 3.44/1.54  #Sup     : 181
% 3.44/1.54  #Fact    : 0
% 3.44/1.54  #Define  : 0
% 3.44/1.54  #Split   : 9
% 3.44/1.54  #Chain   : 0
% 3.44/1.54  #Close   : 0
% 3.44/1.54  
% 3.44/1.54  Ordering : KBO
% 3.44/1.54  
% 3.44/1.54  Simplification rules
% 3.44/1.54  ----------------------
% 3.44/1.54  #Subsume      : 23
% 3.44/1.54  #Demod        : 69
% 3.44/1.54  #Tautology    : 59
% 3.44/1.54  #SimpNegUnit  : 10
% 3.44/1.54  #BackRed      : 20
% 3.44/1.54  
% 3.44/1.54  #Partial instantiations: 0
% 3.44/1.54  #Strategies tried      : 1
% 3.44/1.54  
% 3.44/1.54  Timing (in seconds)
% 3.44/1.54  ----------------------
% 3.44/1.54  Preprocessing        : 0.34
% 3.44/1.54  Parsing              : 0.18
% 3.44/1.54  CNF conversion       : 0.02
% 3.44/1.54  Main loop            : 0.43
% 3.44/1.54  Inferencing          : 0.16
% 3.44/1.54  Reduction            : 0.13
% 3.44/1.54  Demodulation         : 0.09
% 3.44/1.54  BG Simplification    : 0.02
% 3.44/1.54  Subsumption          : 0.07
% 3.44/1.54  Abstraction          : 0.02
% 3.44/1.54  MUC search           : 0.00
% 3.44/1.54  Cooper               : 0.00
% 3.44/1.54  Total                : 0.80
% 3.44/1.54  Index Insertion      : 0.00
% 3.44/1.54  Index Deletion       : 0.00
% 3.44/1.54  Index Matching       : 0.00
% 3.44/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
