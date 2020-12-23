%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:42 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 584 expanded)
%              Number of leaves         :   27 ( 201 expanded)
%              Depth                    :   13
%              Number of atoms          :  226 (1462 expanded)
%              Number of equality atoms :   61 ( 394 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2848,plain,(
    ! [A_315] :
      ( r1_tarski(A_315,k2_zfmisc_1(k1_relat_1(A_315),k2_relat_1(A_315)))
      | ~ v1_relat_1(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k2_zfmisc_1(k1_relat_1(A_8),k2_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1270,plain,(
    ! [A_182,B_183,C_184] :
      ( k1_relset_1(A_182,B_183,C_184) = k1_relat_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1480,plain,(
    ! [A_208,B_209,A_210] :
      ( k1_relset_1(A_208,B_209,A_210) = k1_relat_1(A_210)
      | ~ r1_tarski(A_210,k2_zfmisc_1(A_208,B_209)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1270])).

tff(c_1500,plain,(
    ! [A_8] :
      ( k1_relset_1(k1_relat_1(A_8),k2_relat_1(A_8),A_8) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_1480])).

tff(c_1386,plain,(
    ! [B_191,C_192,A_193] :
      ( k1_xboole_0 = B_191
      | v1_funct_2(C_192,A_193,B_191)
      | k1_relset_1(A_193,B_191,C_192) != A_193
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_193,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2281,plain,(
    ! [B_268,A_269,A_270] :
      ( k1_xboole_0 = B_268
      | v1_funct_2(A_269,A_270,B_268)
      | k1_relset_1(A_270,B_268,A_269) != A_270
      | ~ r1_tarski(A_269,k2_zfmisc_1(A_270,B_268)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1386])).

tff(c_2368,plain,(
    ! [A_277] :
      ( k2_relat_1(A_277) = k1_xboole_0
      | v1_funct_2(A_277,k1_relat_1(A_277),k2_relat_1(A_277))
      | k1_relset_1(k1_relat_1(A_277),k2_relat_1(A_277),A_277) != k1_relat_1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(resolution,[status(thm)],[c_18,c_2281])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_96,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2375,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2368,c_96])).

tff(c_2390,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2375])).

tff(c_2393,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2390])).

tff(c_2396,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1500,c_2393])).

tff(c_2400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2396])).

tff(c_2401,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2390])).

tff(c_2416,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2401,c_18])).

tff(c_2426,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_2416])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2448,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2426,c_2])).

tff(c_251,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_295,plain,(
    ! [A_89,B_90,A_91] :
      ( k1_relset_1(A_89,B_90,A_91) = k1_relat_1(A_91)
      | ~ r1_tarski(A_91,k2_zfmisc_1(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_12,c_251])).

tff(c_309,plain,(
    ! [A_8] :
      ( k1_relset_1(k1_relat_1(A_8),k2_relat_1(A_8),A_8) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_295])).

tff(c_398,plain,(
    ! [B_114,C_115,A_116] :
      ( k1_xboole_0 = B_114
      | v1_funct_2(C_115,A_116,B_114)
      | k1_relset_1(A_116,B_114,C_115) != A_116
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1156,plain,(
    ! [B_175,A_176,A_177] :
      ( k1_xboole_0 = B_175
      | v1_funct_2(A_176,A_177,B_175)
      | k1_relset_1(A_177,B_175,A_176) != A_177
      | ~ r1_tarski(A_176,k2_zfmisc_1(A_177,B_175)) ) ),
    inference(resolution,[status(thm)],[c_12,c_398])).

tff(c_1173,plain,(
    ! [A_178] :
      ( k2_relat_1(A_178) = k1_xboole_0
      | v1_funct_2(A_178,k1_relat_1(A_178),k2_relat_1(A_178))
      | k1_relset_1(k1_relat_1(A_178),k2_relat_1(A_178),A_178) != k1_relat_1(A_178)
      | ~ v1_relat_1(A_178) ) ),
    inference(resolution,[status(thm)],[c_18,c_1156])).

tff(c_1176,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1173,c_96])).

tff(c_1179,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1176])).

tff(c_1180,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1179])).

tff(c_1183,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_1180])).

tff(c_1187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1183])).

tff(c_1188,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1179])).

tff(c_1203,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_18])).

tff(c_1213,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_1203])).

tff(c_144,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_185,plain,(
    ! [C_57,A_58] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_189,plain,(
    ! [A_4,A_58] :
      ( v4_relat_1(A_4,A_58)
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_185])).

tff(c_114,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(k1_relat_1(B_38),A_39)
      | ~ v4_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,(
    ! [A_4,A_29,B_30] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_29,B_30)) ) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_283,plain,(
    ! [B_83,A_84,B_85] :
      ( v1_relat_1(k1_relat_1(B_83))
      | ~ v4_relat_1(B_83,k2_zfmisc_1(A_84,B_85))
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_114,c_89])).

tff(c_292,plain,(
    ! [A_4] :
      ( v1_relat_1(k1_relat_1(A_4))
      | ~ v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_189,c_283])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_206,plain,(
    ! [A_63,A_64,B_65] :
      ( v4_relat_1(A_63,A_64)
      | ~ r1_tarski(A_63,k2_zfmisc_1(A_64,B_65)) ) ),
    inference(resolution,[status(thm)],[c_12,c_144])).

tff(c_345,plain,(
    ! [B_104,A_105,B_106] :
      ( v4_relat_1(k1_relat_1(B_104),A_105)
      | ~ v4_relat_1(B_104,k2_zfmisc_1(A_105,B_106))
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_16,c_206])).

tff(c_353,plain,(
    ! [A_4,A_105] :
      ( v4_relat_1(k1_relat_1(A_4),A_105)
      | ~ v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_189,c_345])).

tff(c_355,plain,(
    ! [A_109,A_110] :
      ( v4_relat_1(k1_relat_1(A_109),A_110)
      | ~ v1_relat_1(A_109)
      | ~ r1_tarski(A_109,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_189,c_345])).

tff(c_129,plain,(
    ! [B_38] :
      ( k1_relat_1(B_38) = k1_xboole_0
      | ~ v4_relat_1(B_38,k1_xboole_0)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_496,plain,(
    ! [A_125] :
      ( k1_relat_1(k1_relat_1(A_125)) = k1_xboole_0
      | ~ v1_relat_1(k1_relat_1(A_125))
      | ~ v1_relat_1(A_125)
      | ~ r1_tarski(A_125,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_355,c_129])).

tff(c_516,plain,(
    ! [A_126] :
      ( k1_relat_1(k1_relat_1(A_126)) = k1_xboole_0
      | ~ v1_relat_1(A_126)
      | ~ r1_tarski(A_126,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_292,c_496])).

tff(c_1049,plain,(
    ! [A_164,A_165] :
      ( r1_tarski(k1_xboole_0,A_164)
      | ~ v4_relat_1(k1_relat_1(A_165),A_164)
      | ~ v1_relat_1(k1_relat_1(A_165))
      | ~ v1_relat_1(A_165)
      | ~ r1_tarski(A_165,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_16])).

tff(c_1084,plain,(
    ! [A_105,A_4] :
      ( r1_tarski(k1_xboole_0,A_105)
      | ~ v1_relat_1(k1_relat_1(A_4))
      | ~ v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_353,c_1049])).

tff(c_1088,plain,(
    ! [A_166] :
      ( ~ v1_relat_1(k1_relat_1(A_166))
      | ~ v1_relat_1(A_166)
      | ~ r1_tarski(A_166,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_1084])).

tff(c_1109,plain,(
    ! [A_4] :
      ( ~ v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_292,c_1088])).

tff(c_1217,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1213,c_1109])).

tff(c_1231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1217])).

tff(c_1232,plain,(
    ! [A_105] : r1_tarski(k1_xboole_0,A_105) ),
    inference(splitRight,[status(thm)],[c_1084])).

tff(c_28,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_49,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_246,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_250,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_246])).

tff(c_1253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_250])).

tff(c_1255,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_86,plain,(
    ! [C_28] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_1268,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1255,c_86])).

tff(c_151,plain,(
    ! [C_45,A_2] :
      ( v4_relat_1(C_45,A_2)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_1299,plain,(
    ! [A_186] : v4_relat_1(k1_xboole_0,A_186) ),
    inference(resolution,[status(thm)],[c_1255,c_151])).

tff(c_1303,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1299,c_129])).

tff(c_1306,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_1303])).

tff(c_1266,plain,(
    ! [A_2] : v4_relat_1(k1_xboole_0,A_2) ),
    inference(resolution,[status(thm)],[c_1255,c_151])).

tff(c_1322,plain,(
    ! [A_6] :
      ( r1_tarski(k1_xboole_0,A_6)
      | ~ v4_relat_1(k1_xboole_0,A_6)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_16])).

tff(c_1334,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_1266,c_1322])).

tff(c_1484,plain,(
    ! [A_208,B_209] : k1_relset_1(A_208,B_209,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1334,c_1480])).

tff(c_1499,plain,(
    ! [A_208,B_209] : k1_relset_1(A_208,B_209,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1484])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1577,plain,(
    ! [C_223,B_224] :
      ( v1_funct_2(C_223,k1_xboole_0,B_224)
      | k1_relset_1(k1_xboole_0,B_224,C_223) != k1_xboole_0
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_1579,plain,(
    ! [B_224] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_224)
      | k1_relset_1(k1_xboole_0,B_224,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1255,c_1577])).

tff(c_1585,plain,(
    ! [B_224] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_1579])).

tff(c_2499,plain,(
    ! [B_224] : v1_funct_2('#skF_1','#skF_1',B_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2448,c_1585])).

tff(c_163,plain,(
    ! [C_50] :
      ( v4_relat_1(C_50,k1_xboole_0)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_144])).

tff(c_169,plain,(
    ! [A_51] :
      ( v4_relat_1(A_51,k1_xboole_0)
      | ~ r1_tarski(A_51,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_163])).

tff(c_173,plain,(
    ! [A_51] :
      ( k1_relat_1(A_51) = k1_xboole_0
      | ~ v1_relat_1(A_51)
      | ~ r1_tarski(A_51,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_169,c_129])).

tff(c_2434,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2426,c_173])).

tff(c_2445,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2434])).

tff(c_2536,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2448,c_2445])).

tff(c_2403,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2401,c_96])).

tff(c_2595,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2536,c_2448,c_2403])).

tff(c_2758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2499,c_2595])).

tff(c_2759,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2765,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_2759])).

tff(c_2854,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2848,c_2765])).

tff(c_2859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:40:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.77  
% 4.46/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.77  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.46/1.77  
% 4.46/1.77  %Foreground sorts:
% 4.46/1.77  
% 4.46/1.77  
% 4.46/1.77  %Background operators:
% 4.46/1.77  
% 4.46/1.77  
% 4.46/1.77  %Foreground operators:
% 4.46/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.46/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.46/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.46/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.46/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.46/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.46/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.46/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.46/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.46/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.77  
% 4.56/1.79  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.56/1.79  tff(f_49, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 4.56/1.79  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.56/1.79  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.56/1.79  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.56/1.79  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.56/1.79  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.56/1.79  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.56/1.79  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.56/1.79  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.56/1.79  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.56/1.79  tff(c_2848, plain, (![A_315]: (r1_tarski(A_315, k2_zfmisc_1(k1_relat_1(A_315), k2_relat_1(A_315))) | ~v1_relat_1(A_315))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.56/1.79  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.79  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.56/1.79  tff(c_18, plain, (![A_8]: (r1_tarski(A_8, k2_zfmisc_1(k1_relat_1(A_8), k2_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.56/1.79  tff(c_1270, plain, (![A_182, B_183, C_184]: (k1_relset_1(A_182, B_183, C_184)=k1_relat_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.56/1.79  tff(c_1480, plain, (![A_208, B_209, A_210]: (k1_relset_1(A_208, B_209, A_210)=k1_relat_1(A_210) | ~r1_tarski(A_210, k2_zfmisc_1(A_208, B_209)))), inference(resolution, [status(thm)], [c_12, c_1270])).
% 4.56/1.79  tff(c_1500, plain, (![A_8]: (k1_relset_1(k1_relat_1(A_8), k2_relat_1(A_8), A_8)=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_18, c_1480])).
% 4.56/1.79  tff(c_1386, plain, (![B_191, C_192, A_193]: (k1_xboole_0=B_191 | v1_funct_2(C_192, A_193, B_191) | k1_relset_1(A_193, B_191, C_192)!=A_193 | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_193, B_191))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.56/1.79  tff(c_2281, plain, (![B_268, A_269, A_270]: (k1_xboole_0=B_268 | v1_funct_2(A_269, A_270, B_268) | k1_relset_1(A_270, B_268, A_269)!=A_270 | ~r1_tarski(A_269, k2_zfmisc_1(A_270, B_268)))), inference(resolution, [status(thm)], [c_12, c_1386])).
% 4.56/1.79  tff(c_2368, plain, (![A_277]: (k2_relat_1(A_277)=k1_xboole_0 | v1_funct_2(A_277, k1_relat_1(A_277), k2_relat_1(A_277)) | k1_relset_1(k1_relat_1(A_277), k2_relat_1(A_277), A_277)!=k1_relat_1(A_277) | ~v1_relat_1(A_277))), inference(resolution, [status(thm)], [c_18, c_2281])).
% 4.56/1.79  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.56/1.79  tff(c_40, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.56/1.79  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 4.56/1.79  tff(c_96, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.56/1.79  tff(c_2375, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2368, c_96])).
% 4.56/1.79  tff(c_2390, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2375])).
% 4.56/1.79  tff(c_2393, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_2390])).
% 4.56/1.79  tff(c_2396, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1500, c_2393])).
% 4.56/1.79  tff(c_2400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2396])).
% 4.56/1.79  tff(c_2401, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2390])).
% 4.56/1.79  tff(c_2416, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2401, c_18])).
% 4.56/1.79  tff(c_2426, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_2416])).
% 4.56/1.79  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.56/1.79  tff(c_2448, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2426, c_2])).
% 4.56/1.79  tff(c_251, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.56/1.79  tff(c_295, plain, (![A_89, B_90, A_91]: (k1_relset_1(A_89, B_90, A_91)=k1_relat_1(A_91) | ~r1_tarski(A_91, k2_zfmisc_1(A_89, B_90)))), inference(resolution, [status(thm)], [c_12, c_251])).
% 4.56/1.79  tff(c_309, plain, (![A_8]: (k1_relset_1(k1_relat_1(A_8), k2_relat_1(A_8), A_8)=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_18, c_295])).
% 4.56/1.79  tff(c_398, plain, (![B_114, C_115, A_116]: (k1_xboole_0=B_114 | v1_funct_2(C_115, A_116, B_114) | k1_relset_1(A_116, B_114, C_115)!=A_116 | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_114))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.56/1.79  tff(c_1156, plain, (![B_175, A_176, A_177]: (k1_xboole_0=B_175 | v1_funct_2(A_176, A_177, B_175) | k1_relset_1(A_177, B_175, A_176)!=A_177 | ~r1_tarski(A_176, k2_zfmisc_1(A_177, B_175)))), inference(resolution, [status(thm)], [c_12, c_398])).
% 4.56/1.79  tff(c_1173, plain, (![A_178]: (k2_relat_1(A_178)=k1_xboole_0 | v1_funct_2(A_178, k1_relat_1(A_178), k2_relat_1(A_178)) | k1_relset_1(k1_relat_1(A_178), k2_relat_1(A_178), A_178)!=k1_relat_1(A_178) | ~v1_relat_1(A_178))), inference(resolution, [status(thm)], [c_18, c_1156])).
% 4.56/1.79  tff(c_1176, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1173, c_96])).
% 4.56/1.79  tff(c_1179, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1176])).
% 4.56/1.79  tff(c_1180, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1179])).
% 4.56/1.79  tff(c_1183, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_309, c_1180])).
% 4.56/1.79  tff(c_1187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1183])).
% 4.56/1.79  tff(c_1188, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1179])).
% 4.56/1.79  tff(c_1203, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1188, c_18])).
% 4.56/1.79  tff(c_1213, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_1203])).
% 4.56/1.79  tff(c_144, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.79  tff(c_185, plain, (![C_57, A_58]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_144])).
% 4.56/1.79  tff(c_189, plain, (![A_4, A_58]: (v4_relat_1(A_4, A_58) | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_185])).
% 4.56/1.79  tff(c_114, plain, (![B_38, A_39]: (r1_tarski(k1_relat_1(B_38), A_39) | ~v4_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.79  tff(c_80, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.56/1.79  tff(c_89, plain, (![A_4, A_29, B_30]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_29, B_30)))), inference(resolution, [status(thm)], [c_12, c_80])).
% 4.56/1.79  tff(c_283, plain, (![B_83, A_84, B_85]: (v1_relat_1(k1_relat_1(B_83)) | ~v4_relat_1(B_83, k2_zfmisc_1(A_84, B_85)) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_114, c_89])).
% 4.56/1.79  tff(c_292, plain, (![A_4]: (v1_relat_1(k1_relat_1(A_4)) | ~v1_relat_1(A_4) | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_189, c_283])).
% 4.56/1.79  tff(c_16, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.79  tff(c_206, plain, (![A_63, A_64, B_65]: (v4_relat_1(A_63, A_64) | ~r1_tarski(A_63, k2_zfmisc_1(A_64, B_65)))), inference(resolution, [status(thm)], [c_12, c_144])).
% 4.56/1.79  tff(c_345, plain, (![B_104, A_105, B_106]: (v4_relat_1(k1_relat_1(B_104), A_105) | ~v4_relat_1(B_104, k2_zfmisc_1(A_105, B_106)) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_16, c_206])).
% 4.56/1.79  tff(c_353, plain, (![A_4, A_105]: (v4_relat_1(k1_relat_1(A_4), A_105) | ~v1_relat_1(A_4) | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_189, c_345])).
% 4.56/1.79  tff(c_355, plain, (![A_109, A_110]: (v4_relat_1(k1_relat_1(A_109), A_110) | ~v1_relat_1(A_109) | ~r1_tarski(A_109, k1_xboole_0))), inference(resolution, [status(thm)], [c_189, c_345])).
% 4.56/1.79  tff(c_129, plain, (![B_38]: (k1_relat_1(B_38)=k1_xboole_0 | ~v4_relat_1(B_38, k1_xboole_0) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_114, c_2])).
% 4.56/1.79  tff(c_496, plain, (![A_125]: (k1_relat_1(k1_relat_1(A_125))=k1_xboole_0 | ~v1_relat_1(k1_relat_1(A_125)) | ~v1_relat_1(A_125) | ~r1_tarski(A_125, k1_xboole_0))), inference(resolution, [status(thm)], [c_355, c_129])).
% 4.56/1.79  tff(c_516, plain, (![A_126]: (k1_relat_1(k1_relat_1(A_126))=k1_xboole_0 | ~v1_relat_1(A_126) | ~r1_tarski(A_126, k1_xboole_0))), inference(resolution, [status(thm)], [c_292, c_496])).
% 4.56/1.79  tff(c_1049, plain, (![A_164, A_165]: (r1_tarski(k1_xboole_0, A_164) | ~v4_relat_1(k1_relat_1(A_165), A_164) | ~v1_relat_1(k1_relat_1(A_165)) | ~v1_relat_1(A_165) | ~r1_tarski(A_165, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_516, c_16])).
% 4.56/1.79  tff(c_1084, plain, (![A_105, A_4]: (r1_tarski(k1_xboole_0, A_105) | ~v1_relat_1(k1_relat_1(A_4)) | ~v1_relat_1(A_4) | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_353, c_1049])).
% 4.56/1.79  tff(c_1088, plain, (![A_166]: (~v1_relat_1(k1_relat_1(A_166)) | ~v1_relat_1(A_166) | ~r1_tarski(A_166, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1084])).
% 4.56/1.79  tff(c_1109, plain, (![A_4]: (~v1_relat_1(A_4) | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_292, c_1088])).
% 4.56/1.79  tff(c_1217, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1213, c_1109])).
% 4.56/1.79  tff(c_1231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1217])).
% 4.56/1.79  tff(c_1232, plain, (![A_105]: (r1_tarski(k1_xboole_0, A_105))), inference(splitRight, [status(thm)], [c_1084])).
% 4.56/1.79  tff(c_28, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.56/1.79  tff(c_49, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 4.56/1.79  tff(c_246, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_49])).
% 4.56/1.79  tff(c_250, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_246])).
% 4.56/1.79  tff(c_1253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1232, c_250])).
% 4.56/1.79  tff(c_1255, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_49])).
% 4.56/1.79  tff(c_86, plain, (![C_28]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_80])).
% 4.56/1.79  tff(c_1268, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1255, c_86])).
% 4.56/1.79  tff(c_151, plain, (![C_45, A_2]: (v4_relat_1(C_45, A_2) | ~m1_subset_1(C_45, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_144])).
% 4.56/1.79  tff(c_1299, plain, (![A_186]: (v4_relat_1(k1_xboole_0, A_186))), inference(resolution, [status(thm)], [c_1255, c_151])).
% 4.56/1.79  tff(c_1303, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1299, c_129])).
% 4.56/1.79  tff(c_1306, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1268, c_1303])).
% 4.56/1.79  tff(c_1266, plain, (![A_2]: (v4_relat_1(k1_xboole_0, A_2))), inference(resolution, [status(thm)], [c_1255, c_151])).
% 4.56/1.79  tff(c_1322, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6) | ~v4_relat_1(k1_xboole_0, A_6) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_16])).
% 4.56/1.79  tff(c_1334, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1268, c_1266, c_1322])).
% 4.56/1.79  tff(c_1484, plain, (![A_208, B_209]: (k1_relset_1(A_208, B_209, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1334, c_1480])).
% 4.56/1.79  tff(c_1499, plain, (![A_208, B_209]: (k1_relset_1(A_208, B_209, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1484])).
% 4.56/1.79  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.56/1.79  tff(c_32, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.56/1.79  tff(c_1577, plain, (![C_223, B_224]: (v1_funct_2(C_223, k1_xboole_0, B_224) | k1_relset_1(k1_xboole_0, B_224, C_223)!=k1_xboole_0 | ~m1_subset_1(C_223, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 4.56/1.79  tff(c_1579, plain, (![B_224]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_224) | k1_relset_1(k1_xboole_0, B_224, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1255, c_1577])).
% 4.56/1.79  tff(c_1585, plain, (![B_224]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_224))), inference(demodulation, [status(thm), theory('equality')], [c_1499, c_1579])).
% 4.56/1.79  tff(c_2499, plain, (![B_224]: (v1_funct_2('#skF_1', '#skF_1', B_224))), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2448, c_1585])).
% 4.56/1.79  tff(c_163, plain, (![C_50]: (v4_relat_1(C_50, k1_xboole_0) | ~m1_subset_1(C_50, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_144])).
% 4.56/1.79  tff(c_169, plain, (![A_51]: (v4_relat_1(A_51, k1_xboole_0) | ~r1_tarski(A_51, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_163])).
% 4.56/1.79  tff(c_173, plain, (![A_51]: (k1_relat_1(A_51)=k1_xboole_0 | ~v1_relat_1(A_51) | ~r1_tarski(A_51, k1_xboole_0))), inference(resolution, [status(thm)], [c_169, c_129])).
% 4.56/1.79  tff(c_2434, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2426, c_173])).
% 4.56/1.79  tff(c_2445, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2434])).
% 4.56/1.79  tff(c_2536, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2448, c_2445])).
% 4.56/1.79  tff(c_2403, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2401, c_96])).
% 4.56/1.79  tff(c_2595, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2536, c_2448, c_2403])).
% 4.56/1.79  tff(c_2758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2499, c_2595])).
% 4.56/1.79  tff(c_2759, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_46])).
% 4.56/1.79  tff(c_2765, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_2759])).
% 4.56/1.79  tff(c_2854, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2848, c_2765])).
% 4.56/1.79  tff(c_2859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2854])).
% 4.56/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.79  
% 4.56/1.79  Inference rules
% 4.56/1.79  ----------------------
% 4.56/1.79  #Ref     : 0
% 4.56/1.79  #Sup     : 630
% 4.56/1.79  #Fact    : 0
% 4.56/1.79  #Define  : 0
% 4.56/1.79  #Split   : 7
% 4.56/1.79  #Chain   : 0
% 4.56/1.79  #Close   : 0
% 4.56/1.79  
% 4.56/1.79  Ordering : KBO
% 4.56/1.79  
% 4.56/1.79  Simplification rules
% 4.56/1.79  ----------------------
% 4.56/1.79  #Subsume      : 193
% 4.56/1.79  #Demod        : 476
% 4.56/1.79  #Tautology    : 239
% 4.56/1.79  #SimpNegUnit  : 2
% 4.56/1.79  #BackRed      : 64
% 4.56/1.79  
% 4.56/1.79  #Partial instantiations: 0
% 4.56/1.79  #Strategies tried      : 1
% 4.56/1.79  
% 4.56/1.79  Timing (in seconds)
% 4.56/1.79  ----------------------
% 4.56/1.80  Preprocessing        : 0.31
% 4.56/1.80  Parsing              : 0.16
% 4.56/1.80  CNF conversion       : 0.02
% 4.56/1.80  Main loop            : 0.71
% 4.56/1.80  Inferencing          : 0.26
% 4.56/1.80  Reduction            : 0.21
% 4.56/1.80  Demodulation         : 0.15
% 4.56/1.80  BG Simplification    : 0.03
% 4.56/1.80  Subsumption          : 0.15
% 4.56/1.80  Abstraction          : 0.04
% 4.56/1.80  MUC search           : 0.00
% 4.56/1.80  Cooper               : 0.00
% 4.56/1.80  Total                : 1.06
% 4.56/1.80  Index Insertion      : 0.00
% 4.56/1.80  Index Deletion       : 0.00
% 4.56/1.80  Index Matching       : 0.00
% 4.56/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
