%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:16 EST 2020

% Result     : Theorem 8.66s
% Output     : CNFRefutation 8.89s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 266 expanded)
%              Number of leaves         :   27 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 525 expanded)
%              Number of equality atoms :   48 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_51,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_34,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(k1_tarski(A_39),B_40) = k1_xboole_0
      | r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_105,c_22])).

tff(c_36,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_160,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_169,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,k4_xboole_0(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_160])).

tff(c_1656,plain,(
    ! [A_137,B_138] : k3_xboole_0(A_137,k4_xboole_0(A_137,B_138)) = k4_xboole_0(A_137,B_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_169])).

tff(c_16686,plain,(
    ! [A_405,B_406] :
      ( k4_xboole_0(k1_tarski(A_405),B_406) = k1_xboole_0
      | r2_hidden(A_405,k4_xboole_0(k1_tarski(A_405),B_406)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1656])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_218,plain,(
    ! [D_57,B_58,A_59] :
      ( ~ r2_hidden(D_57,B_58)
      | ~ r2_hidden(D_57,k4_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3402,plain,(
    ! [A_176,B_177,B_178] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_176,B_177),B_178),B_177)
      | r1_xboole_0(k4_xboole_0(A_176,B_177),B_178) ) ),
    inference(resolution,[status(thm)],[c_32,c_218])).

tff(c_3459,plain,(
    ! [A_179,B_180] : r1_xboole_0(k4_xboole_0(A_179,B_180),B_180) ),
    inference(resolution,[status(thm)],[c_30,c_3402])).

tff(c_3568,plain,(
    ! [A_183,B_184] : k3_xboole_0(k4_xboole_0(A_183,B_184),B_184) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3459,c_22])).

tff(c_253,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_277,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_253])).

tff(c_3619,plain,(
    ! [B_184,A_183] : k4_xboole_0(B_184,k4_xboole_0(A_183,B_184)) = k4_xboole_0(B_184,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3568,c_277])).

tff(c_3706,plain,(
    ! [B_184,A_183] : k4_xboole_0(B_184,k4_xboole_0(A_183,B_184)) = B_184 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3619])).

tff(c_203,plain,(
    ! [D_54,A_55,B_56] :
      ( r2_hidden(D_54,A_55)
      | ~ r2_hidden(D_54,k4_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,(
    ! [A_55,B_56,B_14] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_55,B_56),B_14),A_55)
      | r1_xboole_0(k4_xboole_0(A_55,B_56),B_14) ) ),
    inference(resolution,[status(thm)],[c_32,c_203])).

tff(c_238,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63),B_63)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4468,plain,(
    ! [A_198,A_199,B_200] :
      ( ~ r2_hidden('#skF_3'(A_198,k4_xboole_0(A_199,B_200)),B_200)
      | r1_xboole_0(A_198,k4_xboole_0(A_199,B_200)) ) ),
    inference(resolution,[status(thm)],[c_238,c_6])).

tff(c_4535,plain,(
    ! [A_201,B_202,A_203] : r1_xboole_0(k4_xboole_0(A_201,B_202),k4_xboole_0(A_203,A_201)) ),
    inference(resolution,[status(thm)],[c_217,c_4468])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4776,plain,(
    ! [A_206,A_207,B_208] : r1_xboole_0(k4_xboole_0(A_206,A_207),k4_xboole_0(A_207,B_208)) ),
    inference(resolution,[status(thm)],[c_4535,c_26])).

tff(c_7447,plain,(
    ! [A_270,A_271,B_272] : k3_xboole_0(k4_xboole_0(A_270,A_271),k4_xboole_0(A_271,B_272)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4776,c_22])).

tff(c_10554,plain,(
    ! [B_320,A_321,B_322] : k3_xboole_0(B_320,k4_xboole_0(k4_xboole_0(A_321,B_320),B_322)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3706,c_7447])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_116,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_105,c_50])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k3_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_309,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,B_69)
      | ~ r2_hidden(C_70,A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2049,plain,(
    ! [C_149,B_150,A_151] :
      ( ~ r2_hidden(C_149,B_150)
      | ~ r2_hidden(C_149,A_151)
      | k3_xboole_0(A_151,B_150) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_309])).

tff(c_2080,plain,(
    ! [A_152] :
      ( ~ r2_hidden('#skF_4',A_152)
      | k3_xboole_0(A_152,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_116,c_2049])).

tff(c_2088,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(k4_xboole_0(A_3,B_4),'#skF_5') != k1_xboole_0
      | r2_hidden('#skF_4',B_4)
      | ~ r2_hidden('#skF_4',A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_2080])).

tff(c_2095,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0('#skF_5',k4_xboole_0(A_3,B_4)) != k1_xboole_0
      | r2_hidden('#skF_4',B_4)
      | ~ r2_hidden('#skF_4',A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2088])).

tff(c_10804,plain,(
    ! [B_322,A_321] :
      ( r2_hidden('#skF_4',B_322)
      | ~ r2_hidden('#skF_4',k4_xboole_0(A_321,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10554,c_2095])).

tff(c_11062,plain,(
    ! [A_321] : ~ r2_hidden('#skF_4',k4_xboole_0(A_321,'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10804])).

tff(c_16760,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16686,c_11062])).

tff(c_17002,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16760,c_38])).

tff(c_17087,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34,c_17002])).

tff(c_17089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_17087])).

tff(c_17090,plain,(
    ! [B_322] : r2_hidden('#skF_4',B_322) ),
    inference(splitRight,[status(thm)],[c_10804])).

tff(c_231,plain,(
    ! [D_57,A_18] :
      ( ~ r2_hidden(D_57,k1_xboole_0)
      | ~ r2_hidden(D_57,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_218])).

tff(c_870,plain,(
    ! [A_98,A_99] :
      ( ~ r2_hidden('#skF_3'(A_98,k1_xboole_0),A_99)
      | r1_xboole_0(A_98,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_238,c_231])).

tff(c_943,plain,(
    ! [A_103] : r1_xboole_0(A_103,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_870])).

tff(c_952,plain,(
    ! [A_103] : k3_xboole_0(A_103,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_943,c_22])).

tff(c_955,plain,(
    ! [A_104] : r1_xboole_0(k1_xboole_0,A_104) ),
    inference(resolution,[status(thm)],[c_943,c_26])).

tff(c_964,plain,(
    ! [A_104] : k3_xboole_0(k1_xboole_0,A_104) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_955,c_22])).

tff(c_982,plain,(
    ! [A_108] : k3_xboole_0(A_108,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_943,c_22])).

tff(c_998,plain,(
    ! [A_108] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_277])).

tff(c_1040,plain,(
    ! [A_108] : k4_xboole_0(k1_xboole_0,A_108) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_998])).

tff(c_2809,plain,(
    ! [A_163,B_164] :
      ( k3_xboole_0('#skF_5',k4_xboole_0(A_163,B_164)) != k1_xboole_0
      | r2_hidden('#skF_4',B_164)
      | ~ r2_hidden('#skF_4',A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2088])).

tff(c_4122,plain,(
    ! [A_192,B_193] :
      ( k3_xboole_0('#skF_5',k3_xboole_0(A_192,B_193)) != k1_xboole_0
      | r2_hidden('#skF_4',k4_xboole_0(A_192,B_193))
      | ~ r2_hidden('#skF_4',A_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2809])).

tff(c_2079,plain,(
    ! [A_151] :
      ( ~ r2_hidden('#skF_4',A_151)
      | k3_xboole_0(A_151,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_116,c_2049])).

tff(c_4128,plain,(
    ! [A_192,B_193] :
      ( k3_xboole_0(k4_xboole_0(A_192,B_193),'#skF_5') != k1_xboole_0
      | k3_xboole_0('#skF_5',k3_xboole_0(A_192,B_193)) != k1_xboole_0
      | ~ r2_hidden('#skF_4',A_192) ) ),
    inference(resolution,[status(thm)],[c_4122,c_2079])).

tff(c_4885,plain,(
    ! [A_209,B_210] :
      ( k3_xboole_0('#skF_5',k4_xboole_0(A_209,B_210)) != k1_xboole_0
      | k3_xboole_0('#skF_5',k3_xboole_0(A_209,B_210)) != k1_xboole_0
      | ~ r2_hidden('#skF_4',A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4128])).

tff(c_4917,plain,(
    ! [A_108] :
      ( k3_xboole_0('#skF_5',k1_xboole_0) != k1_xboole_0
      | k3_xboole_0('#skF_5',k3_xboole_0(k1_xboole_0,A_108)) != k1_xboole_0
      | ~ r2_hidden('#skF_4',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_4885])).

tff(c_4948,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_964,c_952,c_4917])).

tff(c_17119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17090,c_4948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:49:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.66/3.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/3.35  
% 8.66/3.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/3.35  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 8.66/3.35  
% 8.66/3.35  %Foreground sorts:
% 8.66/3.35  
% 8.66/3.35  
% 8.66/3.35  %Background operators:
% 8.66/3.35  
% 8.66/3.35  
% 8.66/3.35  %Foreground operators:
% 8.66/3.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.66/3.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.66/3.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.66/3.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.66/3.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.66/3.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.66/3.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.66/3.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.66/3.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.66/3.35  tff('#skF_5', type, '#skF_5': $i).
% 8.66/3.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.66/3.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.66/3.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.66/3.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.66/3.35  tff('#skF_4', type, '#skF_4': $i).
% 8.66/3.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.66/3.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.66/3.35  
% 8.89/3.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.89/3.37  tff(f_85, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 8.89/3.37  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.89/3.37  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.89/3.37  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.89/3.37  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.89/3.37  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.89/3.37  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.89/3.37  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.89/3.37  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.89/3.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.89/3.37  tff(c_48, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.89/3.37  tff(c_51, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 8.89/3.37  tff(c_34, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.89/3.37  tff(c_105, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.89/3.37  tff(c_22, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.89/3.37  tff(c_114, plain, (![A_39, B_40]: (k3_xboole_0(k1_tarski(A_39), B_40)=k1_xboole_0 | r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_105, c_22])).
% 8.89/3.37  tff(c_36, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.89/3.37  tff(c_38, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.89/3.37  tff(c_160, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.89/3.37  tff(c_169, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k3_xboole_0(A_21, k4_xboole_0(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_160])).
% 8.89/3.37  tff(c_1656, plain, (![A_137, B_138]: (k3_xboole_0(A_137, k4_xboole_0(A_137, B_138))=k4_xboole_0(A_137, B_138))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_169])).
% 8.89/3.37  tff(c_16686, plain, (![A_405, B_406]: (k4_xboole_0(k1_tarski(A_405), B_406)=k1_xboole_0 | r2_hidden(A_405, k4_xboole_0(k1_tarski(A_405), B_406)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_1656])).
% 8.89/3.37  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.89/3.37  tff(c_32, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.89/3.37  tff(c_218, plain, (![D_57, B_58, A_59]: (~r2_hidden(D_57, B_58) | ~r2_hidden(D_57, k4_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.89/3.37  tff(c_3402, plain, (![A_176, B_177, B_178]: (~r2_hidden('#skF_3'(k4_xboole_0(A_176, B_177), B_178), B_177) | r1_xboole_0(k4_xboole_0(A_176, B_177), B_178))), inference(resolution, [status(thm)], [c_32, c_218])).
% 8.89/3.37  tff(c_3459, plain, (![A_179, B_180]: (r1_xboole_0(k4_xboole_0(A_179, B_180), B_180))), inference(resolution, [status(thm)], [c_30, c_3402])).
% 8.89/3.37  tff(c_3568, plain, (![A_183, B_184]: (k3_xboole_0(k4_xboole_0(A_183, B_184), B_184)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3459, c_22])).
% 8.89/3.37  tff(c_253, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.89/3.37  tff(c_277, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_253])).
% 8.89/3.37  tff(c_3619, plain, (![B_184, A_183]: (k4_xboole_0(B_184, k4_xboole_0(A_183, B_184))=k4_xboole_0(B_184, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3568, c_277])).
% 8.89/3.37  tff(c_3706, plain, (![B_184, A_183]: (k4_xboole_0(B_184, k4_xboole_0(A_183, B_184))=B_184)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3619])).
% 8.89/3.37  tff(c_203, plain, (![D_54, A_55, B_56]: (r2_hidden(D_54, A_55) | ~r2_hidden(D_54, k4_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.89/3.37  tff(c_217, plain, (![A_55, B_56, B_14]: (r2_hidden('#skF_3'(k4_xboole_0(A_55, B_56), B_14), A_55) | r1_xboole_0(k4_xboole_0(A_55, B_56), B_14))), inference(resolution, [status(thm)], [c_32, c_203])).
% 8.89/3.37  tff(c_238, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63), B_63) | r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.89/3.37  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.89/3.37  tff(c_4468, plain, (![A_198, A_199, B_200]: (~r2_hidden('#skF_3'(A_198, k4_xboole_0(A_199, B_200)), B_200) | r1_xboole_0(A_198, k4_xboole_0(A_199, B_200)))), inference(resolution, [status(thm)], [c_238, c_6])).
% 8.89/3.37  tff(c_4535, plain, (![A_201, B_202, A_203]: (r1_xboole_0(k4_xboole_0(A_201, B_202), k4_xboole_0(A_203, A_201)))), inference(resolution, [status(thm)], [c_217, c_4468])).
% 8.89/3.37  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.89/3.37  tff(c_4776, plain, (![A_206, A_207, B_208]: (r1_xboole_0(k4_xboole_0(A_206, A_207), k4_xboole_0(A_207, B_208)))), inference(resolution, [status(thm)], [c_4535, c_26])).
% 8.89/3.37  tff(c_7447, plain, (![A_270, A_271, B_272]: (k3_xboole_0(k4_xboole_0(A_270, A_271), k4_xboole_0(A_271, B_272))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4776, c_22])).
% 8.89/3.37  tff(c_10554, plain, (![B_320, A_321, B_322]: (k3_xboole_0(B_320, k4_xboole_0(k4_xboole_0(A_321, B_320), B_322))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3706, c_7447])).
% 8.89/3.37  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.89/3.37  tff(c_50, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.89/3.37  tff(c_116, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_105, c_50])).
% 8.89/3.37  tff(c_24, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k3_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.89/3.37  tff(c_309, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, B_69) | ~r2_hidden(C_70, A_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.89/3.37  tff(c_2049, plain, (![C_149, B_150, A_151]: (~r2_hidden(C_149, B_150) | ~r2_hidden(C_149, A_151) | k3_xboole_0(A_151, B_150)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_309])).
% 8.89/3.37  tff(c_2080, plain, (![A_152]: (~r2_hidden('#skF_4', A_152) | k3_xboole_0(A_152, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_116, c_2049])).
% 8.89/3.37  tff(c_2088, plain, (![A_3, B_4]: (k3_xboole_0(k4_xboole_0(A_3, B_4), '#skF_5')!=k1_xboole_0 | r2_hidden('#skF_4', B_4) | ~r2_hidden('#skF_4', A_3))), inference(resolution, [status(thm)], [c_4, c_2080])).
% 8.89/3.37  tff(c_2095, plain, (![A_3, B_4]: (k3_xboole_0('#skF_5', k4_xboole_0(A_3, B_4))!=k1_xboole_0 | r2_hidden('#skF_4', B_4) | ~r2_hidden('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2088])).
% 8.89/3.37  tff(c_10804, plain, (![B_322, A_321]: (r2_hidden('#skF_4', B_322) | ~r2_hidden('#skF_4', k4_xboole_0(A_321, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_10554, c_2095])).
% 8.89/3.37  tff(c_11062, plain, (![A_321]: (~r2_hidden('#skF_4', k4_xboole_0(A_321, '#skF_5')))), inference(splitLeft, [status(thm)], [c_10804])).
% 8.89/3.37  tff(c_16760, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_16686, c_11062])).
% 8.89/3.37  tff(c_17002, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16760, c_38])).
% 8.89/3.37  tff(c_17087, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34, c_17002])).
% 8.89/3.37  tff(c_17089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_17087])).
% 8.89/3.37  tff(c_17090, plain, (![B_322]: (r2_hidden('#skF_4', B_322))), inference(splitRight, [status(thm)], [c_10804])).
% 8.89/3.37  tff(c_231, plain, (![D_57, A_18]: (~r2_hidden(D_57, k1_xboole_0) | ~r2_hidden(D_57, A_18))), inference(superposition, [status(thm), theory('equality')], [c_34, c_218])).
% 8.89/3.37  tff(c_870, plain, (![A_98, A_99]: (~r2_hidden('#skF_3'(A_98, k1_xboole_0), A_99) | r1_xboole_0(A_98, k1_xboole_0))), inference(resolution, [status(thm)], [c_238, c_231])).
% 8.89/3.37  tff(c_943, plain, (![A_103]: (r1_xboole_0(A_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_870])).
% 8.89/3.37  tff(c_952, plain, (![A_103]: (k3_xboole_0(A_103, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_943, c_22])).
% 8.89/3.37  tff(c_955, plain, (![A_104]: (r1_xboole_0(k1_xboole_0, A_104))), inference(resolution, [status(thm)], [c_943, c_26])).
% 8.89/3.37  tff(c_964, plain, (![A_104]: (k3_xboole_0(k1_xboole_0, A_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_955, c_22])).
% 8.89/3.37  tff(c_982, plain, (![A_108]: (k3_xboole_0(A_108, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_943, c_22])).
% 8.89/3.37  tff(c_998, plain, (![A_108]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_108))), inference(superposition, [status(thm), theory('equality')], [c_982, c_277])).
% 8.89/3.37  tff(c_1040, plain, (![A_108]: (k4_xboole_0(k1_xboole_0, A_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_998])).
% 8.89/3.37  tff(c_2809, plain, (![A_163, B_164]: (k3_xboole_0('#skF_5', k4_xboole_0(A_163, B_164))!=k1_xboole_0 | r2_hidden('#skF_4', B_164) | ~r2_hidden('#skF_4', A_163))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2088])).
% 8.89/3.37  tff(c_4122, plain, (![A_192, B_193]: (k3_xboole_0('#skF_5', k3_xboole_0(A_192, B_193))!=k1_xboole_0 | r2_hidden('#skF_4', k4_xboole_0(A_192, B_193)) | ~r2_hidden('#skF_4', A_192))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2809])).
% 8.89/3.37  tff(c_2079, plain, (![A_151]: (~r2_hidden('#skF_4', A_151) | k3_xboole_0(A_151, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_116, c_2049])).
% 8.89/3.37  tff(c_4128, plain, (![A_192, B_193]: (k3_xboole_0(k4_xboole_0(A_192, B_193), '#skF_5')!=k1_xboole_0 | k3_xboole_0('#skF_5', k3_xboole_0(A_192, B_193))!=k1_xboole_0 | ~r2_hidden('#skF_4', A_192))), inference(resolution, [status(thm)], [c_4122, c_2079])).
% 8.89/3.37  tff(c_4885, plain, (![A_209, B_210]: (k3_xboole_0('#skF_5', k4_xboole_0(A_209, B_210))!=k1_xboole_0 | k3_xboole_0('#skF_5', k3_xboole_0(A_209, B_210))!=k1_xboole_0 | ~r2_hidden('#skF_4', A_209))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4128])).
% 8.89/3.37  tff(c_4917, plain, (![A_108]: (k3_xboole_0('#skF_5', k1_xboole_0)!=k1_xboole_0 | k3_xboole_0('#skF_5', k3_xboole_0(k1_xboole_0, A_108))!=k1_xboole_0 | ~r2_hidden('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1040, c_4885])).
% 8.89/3.37  tff(c_4948, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_952, c_964, c_952, c_4917])).
% 8.89/3.37  tff(c_17119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17090, c_4948])).
% 8.89/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.89/3.37  
% 8.89/3.37  Inference rules
% 8.89/3.37  ----------------------
% 8.89/3.37  #Ref     : 0
% 8.89/3.37  #Sup     : 4241
% 8.89/3.37  #Fact    : 0
% 8.89/3.37  #Define  : 0
% 8.89/3.37  #Split   : 2
% 8.89/3.37  #Chain   : 0
% 8.89/3.37  #Close   : 0
% 8.89/3.37  
% 8.89/3.37  Ordering : KBO
% 8.89/3.37  
% 8.89/3.37  Simplification rules
% 8.89/3.37  ----------------------
% 8.89/3.37  #Subsume      : 805
% 8.89/3.37  #Demod        : 4474
% 8.89/3.37  #Tautology    : 2286
% 8.89/3.37  #SimpNegUnit  : 71
% 8.89/3.37  #BackRed      : 13
% 8.89/3.37  
% 8.89/3.37  #Partial instantiations: 0
% 8.89/3.37  #Strategies tried      : 1
% 8.89/3.37  
% 8.89/3.37  Timing (in seconds)
% 8.89/3.37  ----------------------
% 8.89/3.37  Preprocessing        : 0.35
% 8.89/3.38  Parsing              : 0.18
% 8.89/3.38  CNF conversion       : 0.03
% 8.89/3.38  Main loop            : 2.27
% 8.89/3.38  Inferencing          : 0.54
% 8.89/3.38  Reduction            : 1.08
% 8.89/3.38  Demodulation         : 0.92
% 8.89/3.38  BG Simplification    : 0.06
% 8.89/3.38  Subsumption          : 0.46
% 8.89/3.38  Abstraction          : 0.10
% 8.89/3.38  MUC search           : 0.00
% 8.89/3.38  Cooper               : 0.00
% 8.89/3.38  Total                : 2.66
% 8.89/3.38  Index Insertion      : 0.00
% 8.89/3.38  Index Deletion       : 0.00
% 8.89/3.38  Index Matching       : 0.00
% 8.89/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
