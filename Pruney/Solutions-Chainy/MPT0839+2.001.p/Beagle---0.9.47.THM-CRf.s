%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:21 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 277 expanded)
%              Number of leaves         :   37 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 540 expanded)
%              Number of equality atoms :   30 (  84 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2515,plain,(
    ! [A_313,B_314,C_315] :
      ( k2_relset_1(A_313,B_314,C_315) = k2_relat_1(C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2531,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2515])).

tff(c_40,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2538,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2531,c_40])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_93,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_47,c_93])).

tff(c_127,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_140,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_127])).

tff(c_143,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_156,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_143])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_15] :
      ( v1_xboole_0(k2_relat_1(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [A_51] :
      ( v1_xboole_0(k2_relat_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_59,c_6])).

tff(c_75,plain,(
    ! [A_56] :
      ( k2_relat_1(k2_relat_1(A_56)) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_84,plain,(
    ! [A_56] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_22])).

tff(c_109,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(k2_relat_1(A_62))
      | ~ v1_xboole_0(A_62) ) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_116,plain,(
    ! [A_15] : ~ v1_xboole_0(A_15) ),
    inference(resolution,[status(thm)],[c_22,c_109])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_4])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_239,plain,(
    ! [A_95,C_96,B_97] :
      ( m1_subset_1(A_95,C_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(C_96))
      | ~ r2_hidden(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_438,plain,(
    ! [A_126,B_127,A_128] :
      ( m1_subset_1(A_126,B_127)
      | ~ r2_hidden(A_126,A_128)
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(resolution,[status(thm)],[c_14,c_239])).

tff(c_451,plain,(
    ! [A_131,B_132] :
      ( m1_subset_1('#skF_1'(A_131),B_132)
      | ~ r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_117,c_438])).

tff(c_296,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_314,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_296])).

tff(c_121,plain,(
    ! [A_65] : r2_hidden('#skF_1'(A_65),A_65) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_4])).

tff(c_38,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_47,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_126,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_38])).

tff(c_316,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_126])).

tff(c_487,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_451,c_316])).

tff(c_496,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_487])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_156,c_496])).

tff(c_501,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2419,plain,(
    ! [C_298,A_299,B_300] :
      ( v1_xboole_0(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300)))
      | ~ v1_xboole_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2435,plain,(
    ! [A_303,B_304] :
      ( v1_xboole_0(k2_zfmisc_1(A_303,B_304))
      | ~ v1_xboole_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_47,c_2419])).

tff(c_2444,plain,(
    ! [A_305,B_306] :
      ( k2_zfmisc_1(A_305,B_306) = k1_xboole_0
      | ~ v1_xboole_0(A_305) ) ),
    inference(resolution,[status(thm)],[c_2435,c_6])).

tff(c_2452,plain,(
    ! [B_306] : k2_zfmisc_1(k1_xboole_0,B_306) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_501,c_2444])).

tff(c_829,plain,(
    ! [A_184,B_185,C_186] :
      ( k2_relset_1(A_184,B_185,C_186) = k2_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_850,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_829])).

tff(c_852,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_40])).

tff(c_531,plain,(
    ! [C_134,A_135,B_136] :
      ( v1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_544,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_531])).

tff(c_595,plain,(
    ! [C_152,A_153,B_154] :
      ( v4_relat_1(C_152,A_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_608,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_595])).

tff(c_916,plain,(
    ! [D_194,B_195,C_196,A_197] :
      ( m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(B_195,C_196)))
      | ~ r1_tarski(k1_relat_1(D_194),B_195)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_197,C_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1037,plain,(
    ! [B_203] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_203,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_203) ) ),
    inference(resolution,[status(thm)],[c_42,c_916])).

tff(c_30,plain,(
    ! [C_25,A_22,B_23] :
      ( v1_xboole_0(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1074,plain,(
    ! [B_203] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(B_203)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_203) ) ),
    inference(resolution,[status(thm)],[c_1037,c_30])).

tff(c_1218,plain,(
    ! [B_213] :
      ( ~ v1_xboole_0(B_213)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_213) ) ),
    inference(splitLeft,[status(thm)],[c_1074])).

tff(c_1230,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_101,c_1218])).

tff(c_628,plain,(
    ! [A_160,C_161,B_162] :
      ( m1_subset_1(A_160,C_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(C_161))
      | ~ r2_hidden(A_160,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1231,plain,(
    ! [A_214,B_215,A_216] :
      ( m1_subset_1(A_214,B_215)
      | ~ r2_hidden(A_214,A_216)
      | ~ r1_tarski(A_216,B_215) ) ),
    inference(resolution,[status(thm)],[c_14,c_628])).

tff(c_2258,plain,(
    ! [A_283,B_284] :
      ( m1_subset_1('#skF_1'(A_283),B_284)
      | ~ r1_tarski(A_283,B_284)
      | v1_xboole_0(A_283) ) ),
    inference(resolution,[status(thm)],[c_4,c_1231])).

tff(c_782,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_relset_1(A_179,B_180,C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_803,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_782])).

tff(c_511,plain,(
    ! [D_133] :
      ( ~ r2_hidden(D_133,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_133,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_516,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_511])).

tff(c_577,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_823,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_577])).

tff(c_2276,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2258,c_823])).

tff(c_2314,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1230,c_2276])).

tff(c_2325,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_2314])).

tff(c_2329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_608,c_2325])).

tff(c_2330,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1074])).

tff(c_63,plain,(
    ! [A_51] :
      ( k2_relat_1(A_51) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_59,c_6])).

tff(c_2335,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2330,c_63])).

tff(c_2343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_852,c_2335])).

tff(c_2344,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_2353,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2344,c_6])).

tff(c_2626,plain,(
    ! [A_325,B_326,C_327] :
      ( k1_relset_1(A_325,B_326,C_327) = k1_relat_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2640,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2626])).

tff(c_2648,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2353,c_2640])).

tff(c_2806,plain,(
    ! [D_336,B_337,C_338,A_339] :
      ( m1_subset_1(D_336,k1_zfmisc_1(k2_zfmisc_1(B_337,C_338)))
      | ~ r1_tarski(k1_relat_1(D_336),B_337)
      | ~ m1_subset_1(D_336,k1_zfmisc_1(k2_zfmisc_1(A_339,C_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2818,plain,(
    ! [B_337] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_337,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_337) ) ),
    inference(resolution,[status(thm)],[c_42,c_2806])).

tff(c_3068,plain,(
    ! [B_352] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_352,'#skF_2')))
      | ~ r1_tarski(k1_xboole_0,B_352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2648,c_2818])).

tff(c_3101,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2452,c_3068])).

tff(c_3116,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_3101])).

tff(c_2464,plain,(
    ! [B_310] : k2_zfmisc_1(k1_xboole_0,B_310) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_501,c_2444])).

tff(c_2475,plain,(
    ! [C_25] :
      ( v1_xboole_0(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2464,c_30])).

tff(c_2500,plain,(
    ! [C_25] :
      ( v1_xboole_0(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_2475])).

tff(c_3136,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3116,c_2500])).

tff(c_3145,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3136,c_63])).

tff(c_3153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2538,c_3145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:57:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.81  
% 4.53/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.81  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.53/1.81  
% 4.53/1.81  %Foreground sorts:
% 4.53/1.81  
% 4.53/1.81  
% 4.53/1.81  %Background operators:
% 4.53/1.81  
% 4.53/1.81  
% 4.53/1.81  %Foreground operators:
% 4.53/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.53/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.53/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.53/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.53/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.53/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.53/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.53/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.53/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.53/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.53/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.53/1.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.53/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.53/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.53/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.81  
% 4.62/1.84  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 4.62/1.84  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.62/1.84  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.62/1.84  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.62/1.84  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.62/1.84  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.62/1.84  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.62/1.84  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.62/1.84  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 4.62/1.84  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.62/1.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.62/1.84  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.62/1.84  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.62/1.84  tff(f_76, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.62/1.84  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 4.62/1.84  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.62/1.84  tff(c_2515, plain, (![A_313, B_314, C_315]: (k2_relset_1(A_313, B_314, C_315)=k2_relat_1(C_315) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.84  tff(c_2531, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2515])).
% 4.62/1.84  tff(c_40, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.62/1.84  tff(c_2538, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2531, c_40])).
% 4.62/1.84  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.62/1.84  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.84  tff(c_47, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 4.62/1.84  tff(c_93, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.62/1.84  tff(c_101, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_47, c_93])).
% 4.62/1.84  tff(c_127, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.62/1.84  tff(c_140, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_127])).
% 4.62/1.84  tff(c_143, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.62/1.84  tff(c_156, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_143])).
% 4.62/1.84  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.62/1.84  tff(c_22, plain, (![A_15]: (v1_xboole_0(k2_relat_1(A_15)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.62/1.84  tff(c_59, plain, (![A_51]: (v1_xboole_0(k2_relat_1(A_51)) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.62/1.84  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.62/1.84  tff(c_65, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_59, c_6])).
% 4.62/1.84  tff(c_75, plain, (![A_56]: (k2_relat_1(k2_relat_1(A_56))=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_22, c_65])).
% 4.62/1.84  tff(c_84, plain, (![A_56]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_56)) | ~v1_xboole_0(A_56))), inference(superposition, [status(thm), theory('equality')], [c_75, c_22])).
% 4.62/1.84  tff(c_109, plain, (![A_62]: (~v1_xboole_0(k2_relat_1(A_62)) | ~v1_xboole_0(A_62))), inference(splitLeft, [status(thm)], [c_84])).
% 4.62/1.84  tff(c_116, plain, (![A_15]: (~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_22, c_109])).
% 4.62/1.84  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.84  tff(c_117, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_116, c_4])).
% 4.62/1.84  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.62/1.84  tff(c_239, plain, (![A_95, C_96, B_97]: (m1_subset_1(A_95, C_96) | ~m1_subset_1(B_97, k1_zfmisc_1(C_96)) | ~r2_hidden(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.62/1.84  tff(c_438, plain, (![A_126, B_127, A_128]: (m1_subset_1(A_126, B_127) | ~r2_hidden(A_126, A_128) | ~r1_tarski(A_128, B_127))), inference(resolution, [status(thm)], [c_14, c_239])).
% 4.62/1.84  tff(c_451, plain, (![A_131, B_132]: (m1_subset_1('#skF_1'(A_131), B_132) | ~r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_117, c_438])).
% 4.62/1.84  tff(c_296, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.62/1.84  tff(c_314, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_296])).
% 4.62/1.84  tff(c_121, plain, (![A_65]: (r2_hidden('#skF_1'(A_65), A_65))), inference(negUnitSimplification, [status(thm)], [c_116, c_4])).
% 4.62/1.84  tff(c_38, plain, (![D_47]: (~r2_hidden(D_47, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_47, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.62/1.84  tff(c_126, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_121, c_38])).
% 4.62/1.84  tff(c_316, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_126])).
% 4.62/1.84  tff(c_487, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_451, c_316])).
% 4.62/1.84  tff(c_496, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_487])).
% 4.62/1.84  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_156, c_496])).
% 4.62/1.84  tff(c_501, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_84])).
% 4.62/1.84  tff(c_2419, plain, (![C_298, A_299, B_300]: (v1_xboole_0(C_298) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))) | ~v1_xboole_0(A_299))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.62/1.84  tff(c_2435, plain, (![A_303, B_304]: (v1_xboole_0(k2_zfmisc_1(A_303, B_304)) | ~v1_xboole_0(A_303))), inference(resolution, [status(thm)], [c_47, c_2419])).
% 4.62/1.84  tff(c_2444, plain, (![A_305, B_306]: (k2_zfmisc_1(A_305, B_306)=k1_xboole_0 | ~v1_xboole_0(A_305))), inference(resolution, [status(thm)], [c_2435, c_6])).
% 4.62/1.84  tff(c_2452, plain, (![B_306]: (k2_zfmisc_1(k1_xboole_0, B_306)=k1_xboole_0)), inference(resolution, [status(thm)], [c_501, c_2444])).
% 4.62/1.84  tff(c_829, plain, (![A_184, B_185, C_186]: (k2_relset_1(A_184, B_185, C_186)=k2_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.84  tff(c_850, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_829])).
% 4.62/1.84  tff(c_852, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_850, c_40])).
% 4.62/1.84  tff(c_531, plain, (![C_134, A_135, B_136]: (v1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.62/1.84  tff(c_544, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_531])).
% 4.62/1.84  tff(c_595, plain, (![C_152, A_153, B_154]: (v4_relat_1(C_152, A_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.62/1.84  tff(c_608, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_595])).
% 4.62/1.84  tff(c_916, plain, (![D_194, B_195, C_196, A_197]: (m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(B_195, C_196))) | ~r1_tarski(k1_relat_1(D_194), B_195) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_197, C_196))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.62/1.84  tff(c_1037, plain, (![B_203]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_203, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_203))), inference(resolution, [status(thm)], [c_42, c_916])).
% 4.62/1.84  tff(c_30, plain, (![C_25, A_22, B_23]: (v1_xboole_0(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.62/1.84  tff(c_1074, plain, (![B_203]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(B_203) | ~r1_tarski(k1_relat_1('#skF_4'), B_203))), inference(resolution, [status(thm)], [c_1037, c_30])).
% 4.62/1.84  tff(c_1218, plain, (![B_213]: (~v1_xboole_0(B_213) | ~r1_tarski(k1_relat_1('#skF_4'), B_213))), inference(splitLeft, [status(thm)], [c_1074])).
% 4.62/1.84  tff(c_1230, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_101, c_1218])).
% 4.62/1.84  tff(c_628, plain, (![A_160, C_161, B_162]: (m1_subset_1(A_160, C_161) | ~m1_subset_1(B_162, k1_zfmisc_1(C_161)) | ~r2_hidden(A_160, B_162))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.62/1.84  tff(c_1231, plain, (![A_214, B_215, A_216]: (m1_subset_1(A_214, B_215) | ~r2_hidden(A_214, A_216) | ~r1_tarski(A_216, B_215))), inference(resolution, [status(thm)], [c_14, c_628])).
% 4.62/1.84  tff(c_2258, plain, (![A_283, B_284]: (m1_subset_1('#skF_1'(A_283), B_284) | ~r1_tarski(A_283, B_284) | v1_xboole_0(A_283))), inference(resolution, [status(thm)], [c_4, c_1231])).
% 4.62/1.84  tff(c_782, plain, (![A_179, B_180, C_181]: (k1_relset_1(A_179, B_180, C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.62/1.84  tff(c_803, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_782])).
% 4.62/1.84  tff(c_511, plain, (![D_133]: (~r2_hidden(D_133, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_133, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.62/1.84  tff(c_516, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_511])).
% 4.62/1.84  tff(c_577, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_516])).
% 4.62/1.84  tff(c_823, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_803, c_577])).
% 4.62/1.84  tff(c_2276, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2258, c_823])).
% 4.62/1.84  tff(c_2314, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1230, c_2276])).
% 4.62/1.84  tff(c_2325, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_2314])).
% 4.62/1.84  tff(c_2329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_544, c_608, c_2325])).
% 4.62/1.84  tff(c_2330, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1074])).
% 4.62/1.84  tff(c_63, plain, (![A_51]: (k2_relat_1(A_51)=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_59, c_6])).
% 4.62/1.84  tff(c_2335, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2330, c_63])).
% 4.62/1.84  tff(c_2343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_852, c_2335])).
% 4.62/1.84  tff(c_2344, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_516])).
% 4.62/1.84  tff(c_2353, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2344, c_6])).
% 4.62/1.84  tff(c_2626, plain, (![A_325, B_326, C_327]: (k1_relset_1(A_325, B_326, C_327)=k1_relat_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.62/1.84  tff(c_2640, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2626])).
% 4.62/1.84  tff(c_2648, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2353, c_2640])).
% 4.62/1.84  tff(c_2806, plain, (![D_336, B_337, C_338, A_339]: (m1_subset_1(D_336, k1_zfmisc_1(k2_zfmisc_1(B_337, C_338))) | ~r1_tarski(k1_relat_1(D_336), B_337) | ~m1_subset_1(D_336, k1_zfmisc_1(k2_zfmisc_1(A_339, C_338))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.62/1.84  tff(c_2818, plain, (![B_337]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_337, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_337))), inference(resolution, [status(thm)], [c_42, c_2806])).
% 4.62/1.84  tff(c_3068, plain, (![B_352]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_352, '#skF_2'))) | ~r1_tarski(k1_xboole_0, B_352))), inference(demodulation, [status(thm), theory('equality')], [c_2648, c_2818])).
% 4.62/1.84  tff(c_3101, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2452, c_3068])).
% 4.62/1.84  tff(c_3116, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_3101])).
% 4.62/1.84  tff(c_2464, plain, (![B_310]: (k2_zfmisc_1(k1_xboole_0, B_310)=k1_xboole_0)), inference(resolution, [status(thm)], [c_501, c_2444])).
% 4.62/1.84  tff(c_2475, plain, (![C_25]: (v1_xboole_0(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2464, c_30])).
% 4.62/1.84  tff(c_2500, plain, (![C_25]: (v1_xboole_0(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_2475])).
% 4.62/1.84  tff(c_3136, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3116, c_2500])).
% 4.62/1.84  tff(c_3145, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_3136, c_63])).
% 4.62/1.84  tff(c_3153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2538, c_3145])).
% 4.62/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.84  
% 4.62/1.84  Inference rules
% 4.62/1.84  ----------------------
% 4.62/1.84  #Ref     : 0
% 4.62/1.84  #Sup     : 673
% 4.62/1.84  #Fact    : 0
% 4.62/1.84  #Define  : 0
% 4.62/1.84  #Split   : 7
% 4.62/1.84  #Chain   : 0
% 4.62/1.84  #Close   : 0
% 4.62/1.84  
% 4.62/1.84  Ordering : KBO
% 4.62/1.84  
% 4.62/1.84  Simplification rules
% 4.62/1.84  ----------------------
% 4.62/1.84  #Subsume      : 91
% 4.62/1.84  #Demod        : 328
% 4.62/1.84  #Tautology    : 244
% 4.62/1.84  #SimpNegUnit  : 17
% 4.62/1.84  #BackRed      : 23
% 4.62/1.84  
% 4.62/1.84  #Partial instantiations: 0
% 4.62/1.84  #Strategies tried      : 1
% 4.62/1.84  
% 4.62/1.84  Timing (in seconds)
% 4.62/1.84  ----------------------
% 4.62/1.84  Preprocessing        : 0.31
% 4.62/1.84  Parsing              : 0.17
% 4.62/1.84  CNF conversion       : 0.02
% 4.62/1.84  Main loop            : 0.74
% 4.62/1.84  Inferencing          : 0.27
% 4.62/1.84  Reduction            : 0.24
% 4.62/1.84  Demodulation         : 0.17
% 4.62/1.84  BG Simplification    : 0.03
% 4.62/1.84  Subsumption          : 0.13
% 4.62/1.84  Abstraction          : 0.03
% 4.62/1.84  MUC search           : 0.00
% 4.62/1.84  Cooper               : 0.00
% 4.62/1.84  Total                : 1.11
% 4.62/1.84  Index Insertion      : 0.00
% 4.62/1.84  Index Deletion       : 0.00
% 4.62/1.84  Index Matching       : 0.00
% 4.62/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
