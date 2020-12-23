%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:44 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 713 expanded)
%              Number of leaves         :   26 ( 248 expanded)
%              Depth                    :   14
%              Number of atoms          :  243 (1942 expanded)
%              Number of equality atoms :   62 ( 564 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_49,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1611,plain,(
    ! [C_267,A_268,B_269] :
      ( m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ r1_tarski(k2_relat_1(C_267),B_269)
      | ~ r1_tarski(k1_relat_1(C_267),A_268)
      | ~ v1_relat_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_793,plain,(
    ! [C_159,A_160,B_161] :
      ( m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ r1_tarski(k2_relat_1(C_159),B_161)
      | ~ r1_tarski(k1_relat_1(C_159),A_160)
      | ~ v1_relat_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1103,plain,(
    ! [A_203,B_204,C_205] :
      ( k1_relset_1(A_203,B_204,C_205) = k1_relat_1(C_205)
      | ~ r1_tarski(k2_relat_1(C_205),B_204)
      | ~ r1_tarski(k1_relat_1(C_205),A_203)
      | ~ v1_relat_1(C_205) ) ),
    inference(resolution,[status(thm)],[c_793,c_22])).

tff(c_1108,plain,(
    ! [A_206,C_207] :
      ( k1_relset_1(A_206,k2_relat_1(C_207),C_207) = k1_relat_1(C_207)
      | ~ r1_tarski(k1_relat_1(C_207),A_206)
      | ~ v1_relat_1(C_207) ) ),
    inference(resolution,[status(thm)],[c_10,c_1103])).

tff(c_1115,plain,(
    ! [C_207] :
      ( k1_relset_1(k1_relat_1(C_207),k2_relat_1(C_207),C_207) = k1_relat_1(C_207)
      | ~ v1_relat_1(C_207) ) ),
    inference(resolution,[status(thm)],[c_10,c_1108])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ r1_tarski(k2_relat_1(C_18),B_17)
      | ~ r1_tarski(k1_relat_1(C_18),A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_922,plain,(
    ! [B_170,C_171,A_172] :
      ( k1_xboole_0 = B_170
      | v1_funct_2(C_171,A_172,B_170)
      | k1_relset_1(A_172,B_170,C_171) != A_172
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1306,plain,(
    ! [B_234,C_235,A_236] :
      ( k1_xboole_0 = B_234
      | v1_funct_2(C_235,A_236,B_234)
      | k1_relset_1(A_236,B_234,C_235) != A_236
      | ~ r1_tarski(k2_relat_1(C_235),B_234)
      | ~ r1_tarski(k1_relat_1(C_235),A_236)
      | ~ v1_relat_1(C_235) ) ),
    inference(resolution,[status(thm)],[c_24,c_922])).

tff(c_1311,plain,(
    ! [C_237,A_238] :
      ( k2_relat_1(C_237) = k1_xboole_0
      | v1_funct_2(C_237,A_238,k2_relat_1(C_237))
      | k1_relset_1(A_238,k2_relat_1(C_237),C_237) != A_238
      | ~ r1_tarski(k1_relat_1(C_237),A_238)
      | ~ v1_relat_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_10,c_1306])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_97,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1321,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1311,c_97])).

tff(c_1327,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10,c_1321])).

tff(c_1328,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1327])).

tff(c_1331,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_1328])).

tff(c_1335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1331])).

tff(c_1336,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1327])).

tff(c_18,plain,(
    ! [C_9,B_7,A_6] :
      ( v1_xboole_0(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(B_7,A_6)))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1045,plain,(
    ! [C_193,B_194,A_195] :
      ( v1_xboole_0(C_193)
      | ~ v1_xboole_0(B_194)
      | ~ r1_tarski(k2_relat_1(C_193),B_194)
      | ~ r1_tarski(k1_relat_1(C_193),A_195)
      | ~ v1_relat_1(C_193) ) ),
    inference(resolution,[status(thm)],[c_793,c_18])).

tff(c_1050,plain,(
    ! [C_196,A_197] :
      ( v1_xboole_0(C_196)
      | ~ v1_xboole_0(k2_relat_1(C_196))
      | ~ r1_tarski(k1_relat_1(C_196),A_197)
      | ~ v1_relat_1(C_196) ) ),
    inference(resolution,[status(thm)],[c_10,c_1045])).

tff(c_1058,plain,(
    ! [C_196] :
      ( v1_xboole_0(C_196)
      | ~ v1_xboole_0(k2_relat_1(C_196))
      | ~ v1_relat_1(C_196) ) ),
    inference(resolution,[status(thm)],[c_10,c_1050])).

tff(c_1352,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_1058])).

tff(c_1368,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2,c_1352])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1377,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1368,c_4])).

tff(c_226,plain,(
    ! [C_67,A_68,B_69] :
      ( m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ r1_tarski(k2_relat_1(C_67),B_69)
      | ~ r1_tarski(k1_relat_1(C_67),A_68)
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_309,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ r1_tarski(k2_relat_1(C_92),B_91)
      | ~ r1_tarski(k1_relat_1(C_92),A_90)
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_226,c_22])).

tff(c_314,plain,(
    ! [A_93,C_94] :
      ( k1_relset_1(A_93,k2_relat_1(C_94),C_94) = k1_relat_1(C_94)
      | ~ r1_tarski(k1_relat_1(C_94),A_93)
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_10,c_309])).

tff(c_318,plain,(
    ! [C_94] :
      ( k1_relset_1(k1_relat_1(C_94),k2_relat_1(C_94),C_94) = k1_relat_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_10,c_314])).

tff(c_264,plain,(
    ! [B_78,C_79,A_80] :
      ( k1_xboole_0 = B_78
      | v1_funct_2(C_79,A_80,B_78)
      | k1_relset_1(A_80,B_78,C_79) != A_80
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_394,plain,(
    ! [B_113,C_114,A_115] :
      ( k1_xboole_0 = B_113
      | v1_funct_2(C_114,A_115,B_113)
      | k1_relset_1(A_115,B_113,C_114) != A_115
      | ~ r1_tarski(k2_relat_1(C_114),B_113)
      | ~ r1_tarski(k1_relat_1(C_114),A_115)
      | ~ v1_relat_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_24,c_264])).

tff(c_441,plain,(
    ! [C_127,A_128] :
      ( k2_relat_1(C_127) = k1_xboole_0
      | v1_funct_2(C_127,A_128,k2_relat_1(C_127))
      | k1_relset_1(A_128,k2_relat_1(C_127),C_127) != A_128
      | ~ r1_tarski(k1_relat_1(C_127),A_128)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_10,c_394])).

tff(c_449,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_441,c_97])).

tff(c_456,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10,c_449])).

tff(c_457,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_460,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_457])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_460])).

tff(c_465,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_281,plain,(
    ! [C_81,B_82,A_83] :
      ( v1_xboole_0(C_81)
      | ~ v1_xboole_0(B_82)
      | ~ r1_tarski(k2_relat_1(C_81),B_82)
      | ~ r1_tarski(k1_relat_1(C_81),A_83)
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_226,c_18])).

tff(c_286,plain,(
    ! [C_84,A_85] :
      ( v1_xboole_0(C_84)
      | ~ v1_xboole_0(k2_relat_1(C_84))
      | ~ r1_tarski(k1_relat_1(C_84),A_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_10,c_281])).

tff(c_290,plain,(
    ! [C_84] :
      ( v1_xboole_0(C_84)
      | ~ v1_xboole_0(k2_relat_1(C_84))
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_10,c_286])).

tff(c_481,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_290])).

tff(c_497,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2,c_481])).

tff(c_506,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_497,c_4])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [A_19] :
      ( v1_funct_2(k1_xboole_0,A_19,k1_xboole_0)
      | k1_xboole_0 = A_19
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_19,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_47,plain,(
    ! [A_19] :
      ( v1_funct_2(k1_xboole_0,A_19,k1_xboole_0)
      | k1_xboole_0 = A_19
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_108,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_533,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_506,c_108])).

tff(c_235,plain,(
    ! [C_67,A_4] :
      ( m1_subset_1(C_67,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_67),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_67),A_4)
      | ~ v1_relat_1(C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_226])).

tff(c_485,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_4)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_235])).

tff(c_501,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10,c_485])).

tff(c_674,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_501])).

tff(c_676,plain,(
    ! [A_141] : ~ r1_tarski(k1_relat_1('#skF_1'),A_141) ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_674])).

tff(c_681,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_676])).

tff(c_683,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_690,plain,(
    ! [A_143,B_144,C_145] :
      ( k1_relset_1(A_143,B_144,C_145) = k1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_708,plain,(
    ! [B_149,C_150] :
      ( k1_relset_1(k1_xboole_0,B_149,C_150) = k1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_690])).

tff(c_711,plain,(
    ! [B_149] : k1_relset_1(k1_xboole_0,B_149,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_683,c_708])).

tff(c_742,plain,(
    ! [A_156,B_157,C_158] :
      ( m1_subset_1(k1_relset_1(A_156,B_157,C_158),k1_zfmisc_1(A_156))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_763,plain,(
    ! [B_149] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_149))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_742])).

tff(c_776,plain,(
    m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_16,c_763])).

tff(c_98,plain,(
    ! [C_30,B_31,A_32] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(B_31,A_32)))
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [C_30] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_98])).

tff(c_106,plain,(
    ! [C_30] :
      ( v1_xboole_0(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_788,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_776,c_106])).

tff(c_792,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_788,c_4])).

tff(c_697,plain,(
    ! [A_146,C_147] :
      ( k1_relset_1(A_146,k1_xboole_0,C_147) = k1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_690])).

tff(c_700,plain,(
    ! [A_146] : k1_relset_1(A_146,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_683,c_697])).

tff(c_766,plain,(
    ! [A_146] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_146))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_146,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_742])).

tff(c_778,plain,(
    ! [A_146] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_14,c_766])).

tff(c_820,plain,(
    ! [A_162] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_162)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_778])).

tff(c_830,plain,(
    ! [A_13,B_14] : k1_relset_1(A_13,B_14,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_820,c_22])).

tff(c_844,plain,(
    ! [A_13,B_14] : k1_relset_1(A_13,B_14,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_830])).

tff(c_818,plain,(
    ! [A_146] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_778])).

tff(c_30,plain,(
    ! [C_21,B_20] :
      ( v1_funct_2(C_21,k1_xboole_0,B_20)
      | k1_relset_1(k1_xboole_0,B_20,C_21) != k1_xboole_0
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_895,plain,(
    ! [C_167,B_168] :
      ( v1_funct_2(C_167,k1_xboole_0,B_168)
      | k1_relset_1(k1_xboole_0,B_168,C_167) != k1_xboole_0
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_30])).

tff(c_898,plain,(
    ! [B_168] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_168)
      | k1_relset_1(k1_xboole_0,B_168,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_818,c_895])).

tff(c_904,plain,(
    ! [B_168] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_898])).

tff(c_1397,plain,(
    ! [B_168] : v1_funct_2('#skF_1','#skF_1',B_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_1377,c_904])).

tff(c_1401,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_1377,c_792])).

tff(c_1338,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_97])).

tff(c_1491,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1377,c_1338])).

tff(c_1549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1491])).

tff(c_1550,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1620,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1611,c_1550])).

tff(c_1632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10,c_10,c_1620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:36:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.58  
% 3.53/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.59  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.53/1.59  
% 3.53/1.59  %Foreground sorts:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Background operators:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Foreground operators:
% 3.53/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.53/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.59  
% 3.53/1.61  tff(f_94, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.53/1.61  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.61  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.53/1.61  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.53/1.61  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.53/1.61  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.53/1.61  tff(f_49, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.53/1.61  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.53/1.61  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.53/1.61  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.53/1.61  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.53/1.61  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.53/1.61  tff(c_1611, plain, (![C_267, A_268, B_269]: (m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~r1_tarski(k2_relat_1(C_267), B_269) | ~r1_tarski(k1_relat_1(C_267), A_268) | ~v1_relat_1(C_267))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.61  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.53/1.61  tff(c_793, plain, (![C_159, A_160, B_161]: (m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~r1_tarski(k2_relat_1(C_159), B_161) | ~r1_tarski(k1_relat_1(C_159), A_160) | ~v1_relat_1(C_159))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.61  tff(c_22, plain, (![A_13, B_14, C_15]: (k1_relset_1(A_13, B_14, C_15)=k1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.53/1.61  tff(c_1103, plain, (![A_203, B_204, C_205]: (k1_relset_1(A_203, B_204, C_205)=k1_relat_1(C_205) | ~r1_tarski(k2_relat_1(C_205), B_204) | ~r1_tarski(k1_relat_1(C_205), A_203) | ~v1_relat_1(C_205))), inference(resolution, [status(thm)], [c_793, c_22])).
% 3.53/1.61  tff(c_1108, plain, (![A_206, C_207]: (k1_relset_1(A_206, k2_relat_1(C_207), C_207)=k1_relat_1(C_207) | ~r1_tarski(k1_relat_1(C_207), A_206) | ~v1_relat_1(C_207))), inference(resolution, [status(thm)], [c_10, c_1103])).
% 3.53/1.61  tff(c_1115, plain, (![C_207]: (k1_relset_1(k1_relat_1(C_207), k2_relat_1(C_207), C_207)=k1_relat_1(C_207) | ~v1_relat_1(C_207))), inference(resolution, [status(thm)], [c_10, c_1108])).
% 3.53/1.61  tff(c_24, plain, (![C_18, A_16, B_17]: (m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~r1_tarski(k2_relat_1(C_18), B_17) | ~r1_tarski(k1_relat_1(C_18), A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.61  tff(c_922, plain, (![B_170, C_171, A_172]: (k1_xboole_0=B_170 | v1_funct_2(C_171, A_172, B_170) | k1_relset_1(A_172, B_170, C_171)!=A_172 | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_170))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.61  tff(c_1306, plain, (![B_234, C_235, A_236]: (k1_xboole_0=B_234 | v1_funct_2(C_235, A_236, B_234) | k1_relset_1(A_236, B_234, C_235)!=A_236 | ~r1_tarski(k2_relat_1(C_235), B_234) | ~r1_tarski(k1_relat_1(C_235), A_236) | ~v1_relat_1(C_235))), inference(resolution, [status(thm)], [c_24, c_922])).
% 3.53/1.61  tff(c_1311, plain, (![C_237, A_238]: (k2_relat_1(C_237)=k1_xboole_0 | v1_funct_2(C_237, A_238, k2_relat_1(C_237)) | k1_relset_1(A_238, k2_relat_1(C_237), C_237)!=A_238 | ~r1_tarski(k1_relat_1(C_237), A_238) | ~v1_relat_1(C_237))), inference(resolution, [status(thm)], [c_10, c_1306])).
% 3.53/1.61  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.53/1.61  tff(c_38, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.53/1.61  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 3.53/1.61  tff(c_97, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.53/1.61  tff(c_1321, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1311, c_97])).
% 3.53/1.61  tff(c_1327, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10, c_1321])).
% 3.53/1.61  tff(c_1328, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1327])).
% 3.53/1.61  tff(c_1331, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1115, c_1328])).
% 3.53/1.61  tff(c_1335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1331])).
% 3.53/1.61  tff(c_1336, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1327])).
% 3.53/1.61  tff(c_18, plain, (![C_9, B_7, A_6]: (v1_xboole_0(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(B_7, A_6))) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.61  tff(c_1045, plain, (![C_193, B_194, A_195]: (v1_xboole_0(C_193) | ~v1_xboole_0(B_194) | ~r1_tarski(k2_relat_1(C_193), B_194) | ~r1_tarski(k1_relat_1(C_193), A_195) | ~v1_relat_1(C_193))), inference(resolution, [status(thm)], [c_793, c_18])).
% 3.53/1.61  tff(c_1050, plain, (![C_196, A_197]: (v1_xboole_0(C_196) | ~v1_xboole_0(k2_relat_1(C_196)) | ~r1_tarski(k1_relat_1(C_196), A_197) | ~v1_relat_1(C_196))), inference(resolution, [status(thm)], [c_10, c_1045])).
% 3.53/1.61  tff(c_1058, plain, (![C_196]: (v1_xboole_0(C_196) | ~v1_xboole_0(k2_relat_1(C_196)) | ~v1_relat_1(C_196))), inference(resolution, [status(thm)], [c_10, c_1050])).
% 3.53/1.61  tff(c_1352, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1336, c_1058])).
% 3.53/1.61  tff(c_1368, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2, c_1352])).
% 3.53/1.61  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.53/1.61  tff(c_1377, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1368, c_4])).
% 3.53/1.61  tff(c_226, plain, (![C_67, A_68, B_69]: (m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~r1_tarski(k2_relat_1(C_67), B_69) | ~r1_tarski(k1_relat_1(C_67), A_68) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.61  tff(c_309, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~r1_tarski(k2_relat_1(C_92), B_91) | ~r1_tarski(k1_relat_1(C_92), A_90) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_226, c_22])).
% 3.53/1.61  tff(c_314, plain, (![A_93, C_94]: (k1_relset_1(A_93, k2_relat_1(C_94), C_94)=k1_relat_1(C_94) | ~r1_tarski(k1_relat_1(C_94), A_93) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_10, c_309])).
% 3.53/1.61  tff(c_318, plain, (![C_94]: (k1_relset_1(k1_relat_1(C_94), k2_relat_1(C_94), C_94)=k1_relat_1(C_94) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_10, c_314])).
% 3.53/1.61  tff(c_264, plain, (![B_78, C_79, A_80]: (k1_xboole_0=B_78 | v1_funct_2(C_79, A_80, B_78) | k1_relset_1(A_80, B_78, C_79)!=A_80 | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_78))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.61  tff(c_394, plain, (![B_113, C_114, A_115]: (k1_xboole_0=B_113 | v1_funct_2(C_114, A_115, B_113) | k1_relset_1(A_115, B_113, C_114)!=A_115 | ~r1_tarski(k2_relat_1(C_114), B_113) | ~r1_tarski(k1_relat_1(C_114), A_115) | ~v1_relat_1(C_114))), inference(resolution, [status(thm)], [c_24, c_264])).
% 3.53/1.61  tff(c_441, plain, (![C_127, A_128]: (k2_relat_1(C_127)=k1_xboole_0 | v1_funct_2(C_127, A_128, k2_relat_1(C_127)) | k1_relset_1(A_128, k2_relat_1(C_127), C_127)!=A_128 | ~r1_tarski(k1_relat_1(C_127), A_128) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_10, c_394])).
% 3.53/1.61  tff(c_449, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_441, c_97])).
% 3.53/1.61  tff(c_456, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10, c_449])).
% 3.53/1.61  tff(c_457, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_456])).
% 3.53/1.61  tff(c_460, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_318, c_457])).
% 3.53/1.61  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_460])).
% 3.53/1.61  tff(c_465, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_456])).
% 3.53/1.61  tff(c_281, plain, (![C_81, B_82, A_83]: (v1_xboole_0(C_81) | ~v1_xboole_0(B_82) | ~r1_tarski(k2_relat_1(C_81), B_82) | ~r1_tarski(k1_relat_1(C_81), A_83) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_226, c_18])).
% 3.53/1.61  tff(c_286, plain, (![C_84, A_85]: (v1_xboole_0(C_84) | ~v1_xboole_0(k2_relat_1(C_84)) | ~r1_tarski(k1_relat_1(C_84), A_85) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_10, c_281])).
% 3.53/1.61  tff(c_290, plain, (![C_84]: (v1_xboole_0(C_84) | ~v1_xboole_0(k2_relat_1(C_84)) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_10, c_286])).
% 3.53/1.61  tff(c_481, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_465, c_290])).
% 3.53/1.61  tff(c_497, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2, c_481])).
% 3.53/1.61  tff(c_506, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_497, c_4])).
% 3.53/1.61  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.53/1.61  tff(c_26, plain, (![A_19]: (v1_funct_2(k1_xboole_0, A_19, k1_xboole_0) | k1_xboole_0=A_19 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_19, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.61  tff(c_47, plain, (![A_19]: (v1_funct_2(k1_xboole_0, A_19, k1_xboole_0) | k1_xboole_0=A_19 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 3.53/1.61  tff(c_108, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_47])).
% 3.53/1.61  tff(c_533, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_506, c_108])).
% 3.53/1.61  tff(c_235, plain, (![C_67, A_4]: (m1_subset_1(C_67, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_67), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_67), A_4) | ~v1_relat_1(C_67))), inference(superposition, [status(thm), theory('equality')], [c_14, c_226])).
% 3.53/1.61  tff(c_485, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_1'), A_4) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_465, c_235])).
% 3.53/1.61  tff(c_501, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_1'), A_4))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10, c_485])).
% 3.53/1.61  tff(c_674, plain, (![A_4]: (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), A_4))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_501])).
% 3.53/1.61  tff(c_676, plain, (![A_141]: (~r1_tarski(k1_relat_1('#skF_1'), A_141))), inference(negUnitSimplification, [status(thm)], [c_533, c_674])).
% 3.53/1.61  tff(c_681, plain, $false, inference(resolution, [status(thm)], [c_10, c_676])).
% 3.53/1.61  tff(c_683, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_47])).
% 3.53/1.61  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.53/1.61  tff(c_690, plain, (![A_143, B_144, C_145]: (k1_relset_1(A_143, B_144, C_145)=k1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.53/1.61  tff(c_708, plain, (![B_149, C_150]: (k1_relset_1(k1_xboole_0, B_149, C_150)=k1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_690])).
% 3.53/1.61  tff(c_711, plain, (![B_149]: (k1_relset_1(k1_xboole_0, B_149, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_683, c_708])).
% 3.53/1.61  tff(c_742, plain, (![A_156, B_157, C_158]: (m1_subset_1(k1_relset_1(A_156, B_157, C_158), k1_zfmisc_1(A_156)) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.53/1.61  tff(c_763, plain, (![B_149]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_149))))), inference(superposition, [status(thm), theory('equality')], [c_711, c_742])).
% 3.53/1.61  tff(c_776, plain, (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_16, c_763])).
% 3.53/1.61  tff(c_98, plain, (![C_30, B_31, A_32]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(B_31, A_32))) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.61  tff(c_101, plain, (![C_30]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_98])).
% 3.53/1.61  tff(c_106, plain, (![C_30]: (v1_xboole_0(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_101])).
% 3.53/1.61  tff(c_788, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_776, c_106])).
% 3.53/1.61  tff(c_792, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_788, c_4])).
% 3.53/1.61  tff(c_697, plain, (![A_146, C_147]: (k1_relset_1(A_146, k1_xboole_0, C_147)=k1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_690])).
% 3.53/1.61  tff(c_700, plain, (![A_146]: (k1_relset_1(A_146, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_683, c_697])).
% 3.53/1.61  tff(c_766, plain, (![A_146]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_146)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_146, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_700, c_742])).
% 3.53/1.61  tff(c_778, plain, (![A_146]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_146)))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_14, c_766])).
% 3.53/1.61  tff(c_820, plain, (![A_162]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_162)))), inference(demodulation, [status(thm), theory('equality')], [c_792, c_778])).
% 3.53/1.61  tff(c_830, plain, (![A_13, B_14]: (k1_relset_1(A_13, B_14, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_820, c_22])).
% 3.53/1.61  tff(c_844, plain, (![A_13, B_14]: (k1_relset_1(A_13, B_14, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_792, c_830])).
% 3.53/1.61  tff(c_818, plain, (![A_146]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_146)))), inference(demodulation, [status(thm), theory('equality')], [c_792, c_778])).
% 3.53/1.61  tff(c_30, plain, (![C_21, B_20]: (v1_funct_2(C_21, k1_xboole_0, B_20) | k1_relset_1(k1_xboole_0, B_20, C_21)!=k1_xboole_0 | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_20))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.61  tff(c_895, plain, (![C_167, B_168]: (v1_funct_2(C_167, k1_xboole_0, B_168) | k1_relset_1(k1_xboole_0, B_168, C_167)!=k1_xboole_0 | ~m1_subset_1(C_167, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_30])).
% 3.53/1.61  tff(c_898, plain, (![B_168]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_168) | k1_relset_1(k1_xboole_0, B_168, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_818, c_895])).
% 3.53/1.61  tff(c_904, plain, (![B_168]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_844, c_898])).
% 3.53/1.61  tff(c_1397, plain, (![B_168]: (v1_funct_2('#skF_1', '#skF_1', B_168))), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_1377, c_904])).
% 3.53/1.61  tff(c_1401, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_1377, c_792])).
% 3.53/1.61  tff(c_1338, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_97])).
% 3.53/1.61  tff(c_1491, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_1377, c_1338])).
% 3.53/1.61  tff(c_1549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1491])).
% 3.53/1.61  tff(c_1550, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 3.53/1.61  tff(c_1620, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1611, c_1550])).
% 3.53/1.61  tff(c_1632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_10, c_10, c_1620])).
% 3.53/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.61  
% 3.53/1.61  Inference rules
% 3.53/1.61  ----------------------
% 3.53/1.61  #Ref     : 0
% 3.53/1.61  #Sup     : 326
% 3.53/1.61  #Fact    : 0
% 3.53/1.61  #Define  : 0
% 3.53/1.61  #Split   : 5
% 3.53/1.61  #Chain   : 0
% 3.53/1.61  #Close   : 0
% 3.53/1.61  
% 3.53/1.61  Ordering : KBO
% 3.53/1.61  
% 3.53/1.61  Simplification rules
% 3.53/1.61  ----------------------
% 3.53/1.61  #Subsume      : 45
% 3.53/1.61  #Demod        : 446
% 3.53/1.61  #Tautology    : 147
% 3.53/1.61  #SimpNegUnit  : 2
% 3.53/1.61  #BackRed      : 75
% 3.53/1.61  
% 3.53/1.61  #Partial instantiations: 0
% 3.53/1.61  #Strategies tried      : 1
% 3.53/1.61  
% 3.53/1.61  Timing (in seconds)
% 3.53/1.61  ----------------------
% 3.53/1.61  Preprocessing        : 0.31
% 3.53/1.61  Parsing              : 0.16
% 3.53/1.61  CNF conversion       : 0.02
% 3.53/1.61  Main loop            : 0.52
% 3.53/1.61  Inferencing          : 0.18
% 3.53/1.61  Reduction            : 0.16
% 3.53/1.61  Demodulation         : 0.11
% 3.53/1.61  BG Simplification    : 0.03
% 3.53/1.61  Subsumption          : 0.11
% 3.53/1.61  Abstraction          : 0.03
% 3.53/1.61  MUC search           : 0.00
% 3.53/1.61  Cooper               : 0.00
% 3.53/1.61  Total                : 0.88
% 3.53/1.61  Index Insertion      : 0.00
% 3.53/1.62  Index Deletion       : 0.00
% 3.53/1.62  Index Matching       : 0.00
% 3.53/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
