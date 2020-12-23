%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:56 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  178 (1270 expanded)
%              Number of leaves         :   29 ( 402 expanded)
%              Depth                    :   15
%              Number of atoms          :  359 (3591 expanded)
%              Number of equality atoms :  101 ( 815 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_56,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2496,plain,(
    ! [C_424,A_425,B_426] :
      ( m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(A_425,B_426)))
      | ~ r1_tarski(k2_relat_1(C_424),B_426)
      | ~ r1_tarski(k1_relat_1(C_424),A_425)
      | ~ v1_relat_1(C_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_85,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_570,plain,(
    ! [C_121,A_122,B_123] :
      ( m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ r1_tarski(k2_relat_1(C_121),B_123)
      | ~ r1_tarski(k1_relat_1(C_121),A_122)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_612,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ r1_tarski(k2_relat_1(C_131),B_130)
      | ~ r1_tarski(k1_relat_1(C_131),A_129)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_570,c_24])).

tff(c_614,plain,(
    ! [A_129] :
      ( k1_relset_1(A_129,'#skF_2','#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_129)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_612])).

tff(c_625,plain,(
    ! [A_132] :
      ( k1_relset_1(A_132,'#skF_2','#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_614])).

tff(c_630,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_625])).

tff(c_26,plain,(
    ! [C_15,A_13,B_14] :
      ( m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r1_tarski(k2_relat_1(C_15),B_14)
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_631,plain,(
    ! [B_133,C_134,A_135] :
      ( k1_xboole_0 = B_133
      | v1_funct_2(C_134,A_135,B_133)
      | k1_relset_1(A_135,B_133,C_134) != A_135
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1066,plain,(
    ! [B_208,C_209,A_210] :
      ( k1_xboole_0 = B_208
      | v1_funct_2(C_209,A_210,B_208)
      | k1_relset_1(A_210,B_208,C_209) != A_210
      | ~ r1_tarski(k2_relat_1(C_209),B_208)
      | ~ r1_tarski(k1_relat_1(C_209),A_210)
      | ~ v1_relat_1(C_209) ) ),
    inference(resolution,[status(thm)],[c_26,c_631])).

tff(c_1068,plain,(
    ! [A_210] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2('#skF_3',A_210,'#skF_2')
      | k1_relset_1(A_210,'#skF_2','#skF_3') != A_210
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_210)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_1066])).

tff(c_1076,plain,(
    ! [A_210] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2('#skF_3',A_210,'#skF_2')
      | k1_relset_1(A_210,'#skF_2','#skF_3') != A_210
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1068])).

tff(c_1080,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1076])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1007,plain,(
    ! [A_190,B_191,A_192,C_193] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_190,B_191))
      | ~ r2_hidden(A_192,C_193)
      | ~ r1_tarski(k2_relat_1(C_193),B_191)
      | ~ r1_tarski(k1_relat_1(C_193),A_190)
      | ~ v1_relat_1(C_193) ) ),
    inference(resolution,[status(thm)],[c_570,c_18])).

tff(c_1011,plain,(
    ! [A_192,C_193,A_5] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_192,C_193)
      | ~ r1_tarski(k2_relat_1(C_193),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_193),A_5)
      | ~ v1_relat_1(C_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1007])).

tff(c_1056,plain,(
    ! [A_203,C_204,A_205] :
      ( ~ r2_hidden(A_203,C_204)
      | ~ r1_tarski(k2_relat_1(C_204),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_204),A_205)
      | ~ v1_relat_1(C_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1011])).

tff(c_1059,plain,(
    ! [A_1,A_205] :
      ( ~ r1_tarski(k2_relat_1(A_1),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(A_1),A_205)
      | ~ v1_relat_1(A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_1056])).

tff(c_1278,plain,(
    ! [A_231,A_232] :
      ( ~ r1_tarski(k2_relat_1(A_231),'#skF_2')
      | ~ r1_tarski(k1_relat_1(A_231),A_232)
      | ~ v1_relat_1(A_231)
      | A_231 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_1080,c_1059])).

tff(c_1282,plain,(
    ! [A_232] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_232)
      | ~ v1_relat_1('#skF_3')
      | '#skF_2' = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_42,c_1278])).

tff(c_1288,plain,(
    ! [A_232] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_232)
      | '#skF_2' = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1282])).

tff(c_1290,plain,(
    ! [A_233] : ~ r1_tarski(k1_relat_1('#skF_3'),A_233) ),
    inference(splitLeft,[status(thm)],[c_1288])).

tff(c_1295,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_1290])).

tff(c_1296,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1288])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1109,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_1080,c_20])).

tff(c_1315,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_1296,c_1109])).

tff(c_98,plain,(
    ! [B_25,A_26] :
      ( B_25 = A_26
      | ~ r1_tarski(B_25,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_103,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_98])).

tff(c_108,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_1322,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_108])).

tff(c_1407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1315,c_1322])).

tff(c_1410,plain,(
    ! [A_239] :
      ( v1_funct_2('#skF_3',A_239,'#skF_2')
      | k1_relset_1(A_239,'#skF_2','#skF_3') != A_239
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_239) ) ),
    inference(splitRight,[status(thm)],[c_1076])).

tff(c_1414,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1410])).

tff(c_1417,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_1414])).

tff(c_1419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1417])).

tff(c_1420,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_1833,plain,(
    ! [C_324,A_325,B_326] :
      ( m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326)))
      | ~ r1_tarski(k2_relat_1(C_324),B_326)
      | ~ r1_tarski(k1_relat_1(C_324),A_325)
      | ~ v1_relat_1(C_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1912,plain,(
    ! [A_338,B_339,C_340] :
      ( k1_relset_1(A_338,B_339,C_340) = k1_relat_1(C_340)
      | ~ r1_tarski(k2_relat_1(C_340),B_339)
      | ~ r1_tarski(k1_relat_1(C_340),A_338)
      | ~ v1_relat_1(C_340) ) ),
    inference(resolution,[status(thm)],[c_1833,c_24])).

tff(c_1925,plain,(
    ! [A_341,C_342] :
      ( k1_relset_1(A_341,k2_relat_1(C_342),C_342) = k1_relat_1(C_342)
      | ~ r1_tarski(k1_relat_1(C_342),A_341)
      | ~ v1_relat_1(C_342) ) ),
    inference(resolution,[status(thm)],[c_10,c_1912])).

tff(c_1933,plain,(
    ! [C_343] :
      ( k1_relset_1(k1_relat_1(C_343),k2_relat_1(C_343),C_343) = k1_relat_1(C_343)
      | ~ v1_relat_1(C_343) ) ),
    inference(resolution,[status(thm)],[c_10,c_1925])).

tff(c_1942,plain,
    ( k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1933])).

tff(c_1952,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1942])).

tff(c_1878,plain,(
    ! [B_332,C_333,A_334] :
      ( k1_xboole_0 = B_332
      | v1_funct_2(C_333,A_334,B_332)
      | k1_relset_1(A_334,B_332,C_333) != A_334
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_334,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2041,plain,(
    ! [B_368,C_369,A_370] :
      ( k1_xboole_0 = B_368
      | v1_funct_2(C_369,A_370,B_368)
      | k1_relset_1(A_370,B_368,C_369) != A_370
      | ~ r1_tarski(k2_relat_1(C_369),B_368)
      | ~ r1_tarski(k1_relat_1(C_369),A_370)
      | ~ v1_relat_1(C_369) ) ),
    inference(resolution,[status(thm)],[c_26,c_1878])).

tff(c_2043,plain,(
    ! [B_368,A_370] :
      ( k1_xboole_0 = B_368
      | v1_funct_2('#skF_3',A_370,B_368)
      | k1_relset_1(A_370,B_368,'#skF_3') != A_370
      | ~ r1_tarski('#skF_2',B_368)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_370)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_2041])).

tff(c_2053,plain,(
    ! [B_371,A_372] :
      ( k1_xboole_0 = B_371
      | v1_funct_2('#skF_3',A_372,B_371)
      | k1_relset_1(A_372,B_371,'#skF_3') != A_372
      | ~ r1_tarski('#skF_2',B_371)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2043])).

tff(c_2058,plain,(
    ! [B_373] :
      ( k1_xboole_0 = B_373
      | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),B_373)
      | k1_relset_1(k1_relat_1('#skF_3'),B_373,'#skF_3') != k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',B_373) ) ),
    inference(resolution,[status(thm)],[c_10,c_2053])).

tff(c_2066,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2058,c_85])).

tff(c_2073,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1952,c_2066])).

tff(c_1868,plain,(
    ! [C_330,A_331] :
      ( m1_subset_1(C_330,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_330),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_330),A_331)
      | ~ v1_relat_1(C_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1833])).

tff(c_1870,plain,(
    ! [A_331] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_331)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1868])).

tff(c_1874,plain,(
    ! [A_331] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1870])).

tff(c_1877,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1874])).

tff(c_2087,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2073,c_1877])).

tff(c_2109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2087])).

tff(c_2110,plain,(
    ! [A_331] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_331)
      | m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1874])).

tff(c_2117,plain,(
    ! [A_374] : ~ r1_tarski(k1_relat_1('#skF_3'),A_374) ),
    inference(splitLeft,[status(thm)],[c_2110])).

tff(c_2122,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_2117])).

tff(c_2123,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_2110])).

tff(c_2143,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_7,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2123,c_18])).

tff(c_2150,plain,(
    ! [A_378] : ~ r2_hidden(A_378,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2143])).

tff(c_2155,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_2150])).

tff(c_2176,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2155,c_2155,c_20])).

tff(c_2191,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_1420])).

tff(c_2111,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1874])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2114,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_2111,c_6])).

tff(c_2115,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2114])).

tff(c_2158,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2155,c_2115])).

tff(c_2203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2191,c_2158])).

tff(c_2204,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2114])).

tff(c_2386,plain,(
    ! [A_398] :
      ( r2_hidden('#skF_1'(A_398),A_398)
      | A_398 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_4])).

tff(c_2238,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_2])).

tff(c_2245,plain,(
    ! [A_331] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_331)
      | m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_2110])).

tff(c_2304,plain,(
    ! [A_389] : ~ r1_tarski(k1_relat_1('#skF_3'),A_389) ),
    inference(splitLeft,[status(thm)],[c_2245])).

tff(c_2309,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_2304])).

tff(c_2310,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2245])).

tff(c_2313,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_7,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2310,c_18])).

tff(c_2316,plain,(
    ! [A_7] : ~ r2_hidden(A_7,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2238,c_2313])).

tff(c_2395,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2386,c_2316])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1443,plain,(
    ! [C_256,A_257,B_258] :
      ( m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ r1_tarski(k2_relat_1(C_256),B_258)
      | ~ r1_tarski(k1_relat_1(C_256),A_257)
      | ~ v1_relat_1(C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1517,plain,(
    ! [A_270,B_271,C_272] :
      ( k1_relset_1(A_270,B_271,C_272) = k1_relat_1(C_272)
      | ~ r1_tarski(k2_relat_1(C_272),B_271)
      | ~ r1_tarski(k1_relat_1(C_272),A_270)
      | ~ v1_relat_1(C_272) ) ),
    inference(resolution,[status(thm)],[c_1443,c_24])).

tff(c_1529,plain,(
    ! [A_273,C_274] :
      ( k1_relset_1(A_273,k2_relat_1(C_274),C_274) = k1_relat_1(C_274)
      | ~ r1_tarski(k1_relat_1(C_274),A_273)
      | ~ v1_relat_1(C_274) ) ),
    inference(resolution,[status(thm)],[c_10,c_1517])).

tff(c_1537,plain,(
    ! [C_275] :
      ( k1_relset_1(k1_relat_1(C_275),k2_relat_1(C_275),C_275) = k1_relat_1(C_275)
      | ~ v1_relat_1(C_275) ) ),
    inference(resolution,[status(thm)],[c_10,c_1529])).

tff(c_1546,plain,
    ( k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1537])).

tff(c_1556,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1546])).

tff(c_1457,plain,(
    ! [B_259,C_260,A_261] :
      ( k1_xboole_0 = B_259
      | v1_funct_2(C_260,A_261,B_259)
      | k1_relset_1(A_261,B_259,C_260) != A_261
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1597,plain,(
    ! [B_288,C_289,A_290] :
      ( k1_xboole_0 = B_288
      | v1_funct_2(C_289,A_290,B_288)
      | k1_relset_1(A_290,B_288,C_289) != A_290
      | ~ r1_tarski(k2_relat_1(C_289),B_288)
      | ~ r1_tarski(k1_relat_1(C_289),A_290)
      | ~ v1_relat_1(C_289) ) ),
    inference(resolution,[status(thm)],[c_26,c_1457])).

tff(c_1599,plain,(
    ! [B_288,A_290] :
      ( k1_xboole_0 = B_288
      | v1_funct_2('#skF_3',A_290,B_288)
      | k1_relset_1(A_290,B_288,'#skF_3') != A_290
      | ~ r1_tarski('#skF_2',B_288)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_290)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1597])).

tff(c_1634,plain,(
    ! [B_297,A_298] :
      ( k1_xboole_0 = B_297
      | v1_funct_2('#skF_3',A_298,B_297)
      | k1_relset_1(A_298,B_297,'#skF_3') != A_298
      | ~ r1_tarski('#skF_2',B_297)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1599])).

tff(c_1639,plain,(
    ! [B_299] :
      ( k1_xboole_0 = B_299
      | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),B_299)
      | k1_relset_1(k1_relat_1('#skF_3'),B_299,'#skF_3') != k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',B_299) ) ),
    inference(resolution,[status(thm)],[c_10,c_1634])).

tff(c_1645,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1639,c_85])).

tff(c_1649,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1556,c_1645])).

tff(c_1506,plain,(
    ! [C_268,A_269] :
      ( m1_subset_1(C_268,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_268),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_268),A_269)
      | ~ v1_relat_1(C_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1443])).

tff(c_1508,plain,(
    ! [A_269] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_269)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1506])).

tff(c_1512,plain,(
    ! [A_269] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1508])).

tff(c_1516,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1512])).

tff(c_1664,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1516])).

tff(c_1686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1664])).

tff(c_1687,plain,(
    ! [A_269] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_269)
      | m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1512])).

tff(c_1694,plain,(
    ! [A_303] : ~ r1_tarski(k1_relat_1('#skF_3'),A_303) ),
    inference(splitLeft,[status(thm)],[c_1687])).

tff(c_1699,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_1694])).

tff(c_1700,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1687])).

tff(c_1708,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_7,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1700,c_18])).

tff(c_1715,plain,(
    ! [A_304] : ~ r2_hidden(A_304,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1708])).

tff(c_1720,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_1715])).

tff(c_28,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_16,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    ! [A_16] :
      ( v1_funct_2(k1_xboole_0,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_1430,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1469,plain,(
    ! [C_262,B_263] :
      ( m1_subset_1(C_262,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_262),B_263)
      | ~ r1_tarski(k1_relat_1(C_262),k1_xboole_0)
      | ~ v1_relat_1(C_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1443])).

tff(c_1475,plain,(
    ! [B_263] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,B_263)
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1469])).

tff(c_1482,plain,(
    ! [B_263] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,B_263)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22,c_1475])).

tff(c_1483,plain,(
    ! [B_263] :
      ( ~ r1_tarski(k1_xboole_0,B_263)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1430,c_1482])).

tff(c_1485,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1483])).

tff(c_1740,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_1485])).

tff(c_1757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1740])).

tff(c_1760,plain,(
    ! [B_308] : ~ r1_tarski(k1_xboole_0,B_308) ),
    inference(splitRight,[status(thm)],[c_1483])).

tff(c_1765,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_1760])).

tff(c_1767,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_1768,plain,(
    ! [A_309,B_310,C_311] :
      ( k1_relset_1(A_309,B_310,C_311) = k1_relat_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1807,plain,(
    ! [B_319,C_320] :
      ( k1_relset_1(k1_xboole_0,B_319,C_320) = k1_relat_1(C_320)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1768])).

tff(c_1809,plain,(
    ! [B_319] : k1_relset_1(k1_xboole_0,B_319,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1767,c_1807])).

tff(c_1811,plain,(
    ! [B_319] : k1_relset_1(k1_xboole_0,B_319,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1809])).

tff(c_32,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1827,plain,(
    ! [C_322,B_323] :
      ( v1_funct_2(C_322,k1_xboole_0,B_323)
      | k1_relset_1(k1_xboole_0,B_323,C_322) != k1_xboole_0
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_1829,plain,(
    ! [B_323] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_323)
      | k1_relset_1(k1_xboole_0,B_323,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1767,c_1827])).

tff(c_1832,plain,(
    ! [B_323] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_323) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_1829])).

tff(c_2222,plain,(
    ! [B_323] : v1_funct_2('#skF_2','#skF_2',B_323) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_2204,c_1832])).

tff(c_2401,plain,(
    ! [B_323] : v1_funct_2('#skF_3','#skF_3',B_323) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2395,c_2222])).

tff(c_2237,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_2204,c_22])).

tff(c_2406,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2395,c_2237])).

tff(c_2412,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_85])).

tff(c_2456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2401,c_2406,c_2412])).

tff(c_2457,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2504,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2496,c_2457])).

tff(c_2516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10,c_42,c_2504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.85  
% 4.35/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.86  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.35/1.86  
% 4.35/1.86  %Foreground sorts:
% 4.35/1.86  
% 4.35/1.86  
% 4.35/1.86  %Background operators:
% 4.35/1.86  
% 4.35/1.86  
% 4.35/1.86  %Foreground operators:
% 4.35/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.35/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.35/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.35/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.35/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.35/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.35/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.35/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.35/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.35/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.35/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.35/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/1.86  
% 4.74/1.90  tff(f_99, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.74/1.90  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.74/1.90  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.74/1.90  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.74/1.90  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.74/1.90  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.74/1.90  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.74/1.90  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.74/1.90  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.74/1.90  tff(f_56, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.74/1.90  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.74/1.90  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.74/1.90  tff(c_42, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.74/1.90  tff(c_2496, plain, (![C_424, A_425, B_426]: (m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(A_425, B_426))) | ~r1_tarski(k2_relat_1(C_424), B_426) | ~r1_tarski(k1_relat_1(C_424), A_425) | ~v1_relat_1(C_424))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.74/1.90  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.74/1.90  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.74/1.90  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.74/1.90  tff(c_40, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.74/1.90  tff(c_48, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 4.74/1.90  tff(c_85, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 4.74/1.90  tff(c_570, plain, (![C_121, A_122, B_123]: (m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~r1_tarski(k2_relat_1(C_121), B_123) | ~r1_tarski(k1_relat_1(C_121), A_122) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.74/1.90  tff(c_24, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.74/1.90  tff(c_612, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~r1_tarski(k2_relat_1(C_131), B_130) | ~r1_tarski(k1_relat_1(C_131), A_129) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_570, c_24])).
% 4.74/1.90  tff(c_614, plain, (![A_129]: (k1_relset_1(A_129, '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), A_129) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_612])).
% 4.74/1.90  tff(c_625, plain, (![A_132]: (k1_relset_1(A_132, '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), A_132))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_614])).
% 4.74/1.90  tff(c_630, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_625])).
% 4.74/1.90  tff(c_26, plain, (![C_15, A_13, B_14]: (m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~r1_tarski(k2_relat_1(C_15), B_14) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.74/1.90  tff(c_631, plain, (![B_133, C_134, A_135]: (k1_xboole_0=B_133 | v1_funct_2(C_134, A_135, B_133) | k1_relset_1(A_135, B_133, C_134)!=A_135 | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_133))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.74/1.90  tff(c_1066, plain, (![B_208, C_209, A_210]: (k1_xboole_0=B_208 | v1_funct_2(C_209, A_210, B_208) | k1_relset_1(A_210, B_208, C_209)!=A_210 | ~r1_tarski(k2_relat_1(C_209), B_208) | ~r1_tarski(k1_relat_1(C_209), A_210) | ~v1_relat_1(C_209))), inference(resolution, [status(thm)], [c_26, c_631])).
% 4.74/1.90  tff(c_1068, plain, (![A_210]: (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', A_210, '#skF_2') | k1_relset_1(A_210, '#skF_2', '#skF_3')!=A_210 | ~r1_tarski(k1_relat_1('#skF_3'), A_210) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_1066])).
% 4.74/1.90  tff(c_1076, plain, (![A_210]: (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', A_210, '#skF_2') | k1_relset_1(A_210, '#skF_2', '#skF_3')!=A_210 | ~r1_tarski(k1_relat_1('#skF_3'), A_210))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1068])).
% 4.74/1.90  tff(c_1080, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1076])).
% 4.74/1.90  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.74/1.90  tff(c_18, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.74/1.90  tff(c_1007, plain, (![A_190, B_191, A_192, C_193]: (~v1_xboole_0(k2_zfmisc_1(A_190, B_191)) | ~r2_hidden(A_192, C_193) | ~r1_tarski(k2_relat_1(C_193), B_191) | ~r1_tarski(k1_relat_1(C_193), A_190) | ~v1_relat_1(C_193))), inference(resolution, [status(thm)], [c_570, c_18])).
% 4.74/1.90  tff(c_1011, plain, (![A_192, C_193, A_5]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_192, C_193) | ~r1_tarski(k2_relat_1(C_193), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_193), A_5) | ~v1_relat_1(C_193))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1007])).
% 4.74/1.90  tff(c_1056, plain, (![A_203, C_204, A_205]: (~r2_hidden(A_203, C_204) | ~r1_tarski(k2_relat_1(C_204), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_204), A_205) | ~v1_relat_1(C_204))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1011])).
% 4.74/1.90  tff(c_1059, plain, (![A_1, A_205]: (~r1_tarski(k2_relat_1(A_1), k1_xboole_0) | ~r1_tarski(k1_relat_1(A_1), A_205) | ~v1_relat_1(A_1) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_1056])).
% 4.74/1.90  tff(c_1278, plain, (![A_231, A_232]: (~r1_tarski(k2_relat_1(A_231), '#skF_2') | ~r1_tarski(k1_relat_1(A_231), A_232) | ~v1_relat_1(A_231) | A_231='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_1080, c_1059])).
% 4.74/1.90  tff(c_1282, plain, (![A_232]: (~r1_tarski(k1_relat_1('#skF_3'), A_232) | ~v1_relat_1('#skF_3') | '#skF_2'='#skF_3')), inference(resolution, [status(thm)], [c_42, c_1278])).
% 4.74/1.90  tff(c_1288, plain, (![A_232]: (~r1_tarski(k1_relat_1('#skF_3'), A_232) | '#skF_2'='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1282])).
% 4.74/1.90  tff(c_1290, plain, (![A_233]: (~r1_tarski(k1_relat_1('#skF_3'), A_233))), inference(splitLeft, [status(thm)], [c_1288])).
% 4.74/1.90  tff(c_1295, plain, $false, inference(resolution, [status(thm)], [c_10, c_1290])).
% 4.74/1.90  tff(c_1296, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1288])).
% 4.74/1.90  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.74/1.90  tff(c_1109, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_1080, c_20])).
% 4.74/1.90  tff(c_1315, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_1296, c_1109])).
% 4.74/1.90  tff(c_98, plain, (![B_25, A_26]: (B_25=A_26 | ~r1_tarski(B_25, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.74/1.90  tff(c_103, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_98])).
% 4.74/1.90  tff(c_108, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_103])).
% 4.74/1.90  tff(c_1322, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_108])).
% 4.74/1.90  tff(c_1407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1315, c_1322])).
% 4.74/1.90  tff(c_1410, plain, (![A_239]: (v1_funct_2('#skF_3', A_239, '#skF_2') | k1_relset_1(A_239, '#skF_2', '#skF_3')!=A_239 | ~r1_tarski(k1_relat_1('#skF_3'), A_239))), inference(splitRight, [status(thm)], [c_1076])).
% 4.74/1.90  tff(c_1414, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1410])).
% 4.74/1.90  tff(c_1417, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_630, c_1414])).
% 4.74/1.90  tff(c_1419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_1417])).
% 4.74/1.90  tff(c_1420, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_103])).
% 4.74/1.90  tff(c_1833, plain, (![C_324, A_325, B_326]: (m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))) | ~r1_tarski(k2_relat_1(C_324), B_326) | ~r1_tarski(k1_relat_1(C_324), A_325) | ~v1_relat_1(C_324))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.74/1.90  tff(c_1912, plain, (![A_338, B_339, C_340]: (k1_relset_1(A_338, B_339, C_340)=k1_relat_1(C_340) | ~r1_tarski(k2_relat_1(C_340), B_339) | ~r1_tarski(k1_relat_1(C_340), A_338) | ~v1_relat_1(C_340))), inference(resolution, [status(thm)], [c_1833, c_24])).
% 4.74/1.90  tff(c_1925, plain, (![A_341, C_342]: (k1_relset_1(A_341, k2_relat_1(C_342), C_342)=k1_relat_1(C_342) | ~r1_tarski(k1_relat_1(C_342), A_341) | ~v1_relat_1(C_342))), inference(resolution, [status(thm)], [c_10, c_1912])).
% 4.74/1.90  tff(c_1933, plain, (![C_343]: (k1_relset_1(k1_relat_1(C_343), k2_relat_1(C_343), C_343)=k1_relat_1(C_343) | ~v1_relat_1(C_343))), inference(resolution, [status(thm)], [c_10, c_1925])).
% 4.74/1.90  tff(c_1942, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1933])).
% 4.74/1.90  tff(c_1952, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1942])).
% 4.74/1.90  tff(c_1878, plain, (![B_332, C_333, A_334]: (k1_xboole_0=B_332 | v1_funct_2(C_333, A_334, B_332) | k1_relset_1(A_334, B_332, C_333)!=A_334 | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_334, B_332))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.74/1.90  tff(c_2041, plain, (![B_368, C_369, A_370]: (k1_xboole_0=B_368 | v1_funct_2(C_369, A_370, B_368) | k1_relset_1(A_370, B_368, C_369)!=A_370 | ~r1_tarski(k2_relat_1(C_369), B_368) | ~r1_tarski(k1_relat_1(C_369), A_370) | ~v1_relat_1(C_369))), inference(resolution, [status(thm)], [c_26, c_1878])).
% 4.74/1.90  tff(c_2043, plain, (![B_368, A_370]: (k1_xboole_0=B_368 | v1_funct_2('#skF_3', A_370, B_368) | k1_relset_1(A_370, B_368, '#skF_3')!=A_370 | ~r1_tarski('#skF_2', B_368) | ~r1_tarski(k1_relat_1('#skF_3'), A_370) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_2041])).
% 4.74/1.90  tff(c_2053, plain, (![B_371, A_372]: (k1_xboole_0=B_371 | v1_funct_2('#skF_3', A_372, B_371) | k1_relset_1(A_372, B_371, '#skF_3')!=A_372 | ~r1_tarski('#skF_2', B_371) | ~r1_tarski(k1_relat_1('#skF_3'), A_372))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2043])).
% 4.74/1.90  tff(c_2058, plain, (![B_373]: (k1_xboole_0=B_373 | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), B_373) | k1_relset_1(k1_relat_1('#skF_3'), B_373, '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', B_373))), inference(resolution, [status(thm)], [c_10, c_2053])).
% 4.74/1.90  tff(c_2066, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2058, c_85])).
% 4.74/1.90  tff(c_2073, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1952, c_2066])).
% 4.74/1.90  tff(c_1868, plain, (![C_330, A_331]: (m1_subset_1(C_330, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_330), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_330), A_331) | ~v1_relat_1(C_330))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1833])).
% 4.74/1.90  tff(c_1870, plain, (![A_331]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_331) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1868])).
% 4.74/1.90  tff(c_1874, plain, (![A_331]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_331))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1870])).
% 4.74/1.90  tff(c_1877, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1874])).
% 4.74/1.90  tff(c_2087, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2073, c_1877])).
% 4.74/1.90  tff(c_2109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_2087])).
% 4.74/1.90  tff(c_2110, plain, (![A_331]: (~r1_tarski(k1_relat_1('#skF_3'), A_331) | m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1874])).
% 4.74/1.90  tff(c_2117, plain, (![A_374]: (~r1_tarski(k1_relat_1('#skF_3'), A_374))), inference(splitLeft, [status(thm)], [c_2110])).
% 4.74/1.90  tff(c_2122, plain, $false, inference(resolution, [status(thm)], [c_10, c_2117])).
% 4.74/1.90  tff(c_2123, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_2110])).
% 4.74/1.90  tff(c_2143, plain, (![A_7]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_7, '#skF_3'))), inference(resolution, [status(thm)], [c_2123, c_18])).
% 4.74/1.90  tff(c_2150, plain, (![A_378]: (~r2_hidden(A_378, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2143])).
% 4.74/1.90  tff(c_2155, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_2150])).
% 4.74/1.90  tff(c_2176, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2155, c_2155, c_20])).
% 4.74/1.90  tff(c_2191, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_1420])).
% 4.74/1.90  tff(c_2111, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1874])).
% 4.74/1.90  tff(c_6, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.74/1.90  tff(c_2114, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_2111, c_6])).
% 4.74/1.90  tff(c_2115, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_2114])).
% 4.74/1.90  tff(c_2158, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2155, c_2115])).
% 4.74/1.90  tff(c_2203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_2191, c_2158])).
% 4.74/1.90  tff(c_2204, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2114])).
% 4.74/1.90  tff(c_2386, plain, (![A_398]: (r2_hidden('#skF_1'(A_398), A_398) | A_398='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_4])).
% 4.74/1.90  tff(c_2238, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_2])).
% 4.74/1.90  tff(c_2245, plain, (![A_331]: (~r1_tarski(k1_relat_1('#skF_3'), A_331) | m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_2110])).
% 4.74/1.90  tff(c_2304, plain, (![A_389]: (~r1_tarski(k1_relat_1('#skF_3'), A_389))), inference(splitLeft, [status(thm)], [c_2245])).
% 4.74/1.90  tff(c_2309, plain, $false, inference(resolution, [status(thm)], [c_10, c_2304])).
% 4.74/1.90  tff(c_2310, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2245])).
% 4.74/1.90  tff(c_2313, plain, (![A_7]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_7, '#skF_3'))), inference(resolution, [status(thm)], [c_2310, c_18])).
% 4.74/1.90  tff(c_2316, plain, (![A_7]: (~r2_hidden(A_7, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2238, c_2313])).
% 4.74/1.90  tff(c_2395, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_2386, c_2316])).
% 4.74/1.90  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.74/1.90  tff(c_1443, plain, (![C_256, A_257, B_258]: (m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~r1_tarski(k2_relat_1(C_256), B_258) | ~r1_tarski(k1_relat_1(C_256), A_257) | ~v1_relat_1(C_256))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.74/1.90  tff(c_1517, plain, (![A_270, B_271, C_272]: (k1_relset_1(A_270, B_271, C_272)=k1_relat_1(C_272) | ~r1_tarski(k2_relat_1(C_272), B_271) | ~r1_tarski(k1_relat_1(C_272), A_270) | ~v1_relat_1(C_272))), inference(resolution, [status(thm)], [c_1443, c_24])).
% 4.74/1.90  tff(c_1529, plain, (![A_273, C_274]: (k1_relset_1(A_273, k2_relat_1(C_274), C_274)=k1_relat_1(C_274) | ~r1_tarski(k1_relat_1(C_274), A_273) | ~v1_relat_1(C_274))), inference(resolution, [status(thm)], [c_10, c_1517])).
% 4.74/1.90  tff(c_1537, plain, (![C_275]: (k1_relset_1(k1_relat_1(C_275), k2_relat_1(C_275), C_275)=k1_relat_1(C_275) | ~v1_relat_1(C_275))), inference(resolution, [status(thm)], [c_10, c_1529])).
% 4.74/1.90  tff(c_1546, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1537])).
% 4.74/1.90  tff(c_1556, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1546])).
% 4.74/1.90  tff(c_1457, plain, (![B_259, C_260, A_261]: (k1_xboole_0=B_259 | v1_funct_2(C_260, A_261, B_259) | k1_relset_1(A_261, B_259, C_260)!=A_261 | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_259))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.74/1.90  tff(c_1597, plain, (![B_288, C_289, A_290]: (k1_xboole_0=B_288 | v1_funct_2(C_289, A_290, B_288) | k1_relset_1(A_290, B_288, C_289)!=A_290 | ~r1_tarski(k2_relat_1(C_289), B_288) | ~r1_tarski(k1_relat_1(C_289), A_290) | ~v1_relat_1(C_289))), inference(resolution, [status(thm)], [c_26, c_1457])).
% 4.74/1.90  tff(c_1599, plain, (![B_288, A_290]: (k1_xboole_0=B_288 | v1_funct_2('#skF_3', A_290, B_288) | k1_relset_1(A_290, B_288, '#skF_3')!=A_290 | ~r1_tarski('#skF_2', B_288) | ~r1_tarski(k1_relat_1('#skF_3'), A_290) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1597])).
% 4.74/1.90  tff(c_1634, plain, (![B_297, A_298]: (k1_xboole_0=B_297 | v1_funct_2('#skF_3', A_298, B_297) | k1_relset_1(A_298, B_297, '#skF_3')!=A_298 | ~r1_tarski('#skF_2', B_297) | ~r1_tarski(k1_relat_1('#skF_3'), A_298))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1599])).
% 4.74/1.90  tff(c_1639, plain, (![B_299]: (k1_xboole_0=B_299 | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), B_299) | k1_relset_1(k1_relat_1('#skF_3'), B_299, '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', B_299))), inference(resolution, [status(thm)], [c_10, c_1634])).
% 4.74/1.90  tff(c_1645, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1639, c_85])).
% 4.74/1.90  tff(c_1649, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1556, c_1645])).
% 4.74/1.90  tff(c_1506, plain, (![C_268, A_269]: (m1_subset_1(C_268, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_268), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_268), A_269) | ~v1_relat_1(C_268))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1443])).
% 4.74/1.90  tff(c_1508, plain, (![A_269]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_269) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1506])).
% 4.74/1.90  tff(c_1512, plain, (![A_269]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_269))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1508])).
% 4.74/1.90  tff(c_1516, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1512])).
% 4.74/1.90  tff(c_1664, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1516])).
% 4.74/1.90  tff(c_1686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1664])).
% 4.74/1.90  tff(c_1687, plain, (![A_269]: (~r1_tarski(k1_relat_1('#skF_3'), A_269) | m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1512])).
% 4.74/1.90  tff(c_1694, plain, (![A_303]: (~r1_tarski(k1_relat_1('#skF_3'), A_303))), inference(splitLeft, [status(thm)], [c_1687])).
% 4.74/1.90  tff(c_1699, plain, $false, inference(resolution, [status(thm)], [c_10, c_1694])).
% 4.74/1.90  tff(c_1700, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1687])).
% 4.74/1.90  tff(c_1708, plain, (![A_7]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_7, '#skF_3'))), inference(resolution, [status(thm)], [c_1700, c_18])).
% 4.74/1.90  tff(c_1715, plain, (![A_304]: (~r2_hidden(A_304, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1708])).
% 4.74/1.90  tff(c_1720, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_1715])).
% 4.74/1.90  tff(c_28, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_16, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.74/1.90  tff(c_51, plain, (![A_16]: (v1_funct_2(k1_xboole_0, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 4.74/1.90  tff(c_1430, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_51])).
% 4.74/1.90  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.74/1.90  tff(c_1469, plain, (![C_262, B_263]: (m1_subset_1(C_262, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_262), B_263) | ~r1_tarski(k1_relat_1(C_262), k1_xboole_0) | ~v1_relat_1(C_262))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1443])).
% 4.74/1.90  tff(c_1475, plain, (![B_263]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, B_263) | ~r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1469])).
% 4.74/1.90  tff(c_1482, plain, (![B_263]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, B_263) | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22, c_1475])).
% 4.74/1.90  tff(c_1483, plain, (![B_263]: (~r1_tarski(k1_xboole_0, B_263) | ~v1_relat_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1430, c_1482])).
% 4.74/1.90  tff(c_1485, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1483])).
% 4.74/1.90  tff(c_1740, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1720, c_1485])).
% 4.74/1.90  tff(c_1757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1740])).
% 4.74/1.91  tff(c_1760, plain, (![B_308]: (~r1_tarski(k1_xboole_0, B_308))), inference(splitRight, [status(thm)], [c_1483])).
% 4.74/1.91  tff(c_1765, plain, $false, inference(resolution, [status(thm)], [c_10, c_1760])).
% 4.74/1.91  tff(c_1767, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_51])).
% 4.74/1.91  tff(c_1768, plain, (![A_309, B_310, C_311]: (k1_relset_1(A_309, B_310, C_311)=k1_relat_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.74/1.91  tff(c_1807, plain, (![B_319, C_320]: (k1_relset_1(k1_xboole_0, B_319, C_320)=k1_relat_1(C_320) | ~m1_subset_1(C_320, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1768])).
% 4.74/1.91  tff(c_1809, plain, (![B_319]: (k1_relset_1(k1_xboole_0, B_319, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1767, c_1807])).
% 4.74/1.91  tff(c_1811, plain, (![B_319]: (k1_relset_1(k1_xboole_0, B_319, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1809])).
% 4.74/1.91  tff(c_32, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.74/1.91  tff(c_1827, plain, (![C_322, B_323]: (v1_funct_2(C_322, k1_xboole_0, B_323) | k1_relset_1(k1_xboole_0, B_323, C_322)!=k1_xboole_0 | ~m1_subset_1(C_322, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 4.74/1.91  tff(c_1829, plain, (![B_323]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_323) | k1_relset_1(k1_xboole_0, B_323, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1767, c_1827])).
% 4.74/1.91  tff(c_1832, plain, (![B_323]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_323))), inference(demodulation, [status(thm), theory('equality')], [c_1811, c_1829])).
% 4.74/1.91  tff(c_2222, plain, (![B_323]: (v1_funct_2('#skF_2', '#skF_2', B_323))), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_2204, c_1832])).
% 4.74/1.91  tff(c_2401, plain, (![B_323]: (v1_funct_2('#skF_3', '#skF_3', B_323))), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2395, c_2222])).
% 4.74/1.91  tff(c_2237, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_2204, c_22])).
% 4.74/1.91  tff(c_2406, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2395, c_2237])).
% 4.74/1.91  tff(c_2412, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2395, c_85])).
% 4.74/1.91  tff(c_2456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2401, c_2406, c_2412])).
% 4.74/1.91  tff(c_2457, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_48])).
% 4.74/1.91  tff(c_2504, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2496, c_2457])).
% 4.74/1.91  tff(c_2516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_10, c_42, c_2504])).
% 4.74/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.91  
% 4.74/1.91  Inference rules
% 4.74/1.91  ----------------------
% 4.74/1.91  #Ref     : 0
% 4.74/1.91  #Sup     : 487
% 4.74/1.91  #Fact    : 0
% 4.74/1.91  #Define  : 0
% 4.74/1.91  #Split   : 27
% 4.74/1.91  #Chain   : 0
% 4.74/1.91  #Close   : 0
% 4.74/1.91  
% 4.74/1.91  Ordering : KBO
% 4.74/1.91  
% 4.74/1.91  Simplification rules
% 4.74/1.91  ----------------------
% 4.74/1.91  #Subsume      : 99
% 4.74/1.91  #Demod        : 906
% 4.74/1.91  #Tautology    : 225
% 4.74/1.91  #SimpNegUnit  : 10
% 4.74/1.91  #BackRed      : 310
% 4.74/1.91  
% 4.74/1.91  #Partial instantiations: 0
% 4.74/1.91  #Strategies tried      : 1
% 4.74/1.91  
% 4.74/1.91  Timing (in seconds)
% 4.74/1.91  ----------------------
% 4.74/1.91  Preprocessing        : 0.34
% 4.74/1.91  Parsing              : 0.18
% 4.74/1.91  CNF conversion       : 0.02
% 4.74/1.91  Main loop            : 0.68
% 4.74/1.91  Inferencing          : 0.23
% 4.74/1.91  Reduction            : 0.22
% 4.74/1.91  Demodulation         : 0.15
% 4.74/1.91  BG Simplification    : 0.03
% 4.74/1.91  Subsumption          : 0.14
% 4.74/1.91  Abstraction          : 0.04
% 4.74/1.91  MUC search           : 0.00
% 4.74/1.91  Cooper               : 0.00
% 4.74/1.91  Total                : 1.12
% 4.74/1.91  Index Insertion      : 0.00
% 4.74/1.91  Index Deletion       : 0.00
% 4.74/1.91  Index Matching       : 0.00
% 4.74/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
