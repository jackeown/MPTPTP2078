%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:21 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 327 expanded)
%              Number of leaves         :   27 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  190 ( 795 expanded)
%              Number of equality atoms :   25 (  69 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_60,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_110,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(B_38,A_39)
      | ~ v1_xboole_0(B_38)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,(
    ! [A_35] :
      ( v1_xboole_0(A_35)
      | r2_hidden('#skF_1'(A_35),A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_6')
      | ~ m1_subset_1(C_24,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_102,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_89,c_42])).

tff(c_104,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_118,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_104])).

tff(c_119,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [B_54,A_55] :
      ( m1_subset_1(B_54,A_55)
      | ~ r2_hidden(B_54,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_205,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_193])).

tff(c_155,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | ~ m1_subset_1(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_179,plain,(
    ! [B_50] :
      ( ~ m1_subset_1(B_50,'#skF_5')
      | ~ m1_subset_1(B_50,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_155,c_42])).

tff(c_257,plain,(
    ! [B_66] :
      ( ~ m1_subset_1(B_66,'#skF_5')
      | ~ m1_subset_1(B_66,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_261,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_205,c_257])).

tff(c_268,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_261])).

tff(c_273,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_268])).

tff(c_274,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_19] : k3_tarski(k1_zfmisc_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_120,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,k3_tarski(B_41))
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [A_40,A_19] :
      ( r1_tarski(A_40,A_19)
      | ~ r2_hidden(A_40,k1_zfmisc_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_120])).

tff(c_159,plain,(
    ! [B_50,A_19] :
      ( r1_tarski(B_50,A_19)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_155,c_123])).

tff(c_183,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_159])).

tff(c_192,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_183])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( r2_hidden(B_21,A_20)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_247,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1000,plain,(
    ! [B_119,B_120,A_121] :
      ( r2_hidden(B_119,B_120)
      | ~ r1_tarski(A_121,B_120)
      | ~ m1_subset_1(B_119,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_34,c_247])).

tff(c_1006,plain,(
    ! [B_119] :
      ( r2_hidden(B_119,'#skF_5')
      | ~ m1_subset_1(B_119,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_192,c_1000])).

tff(c_1025,plain,(
    ! [B_122] :
      ( r2_hidden(B_122,'#skF_5')
      | ~ m1_subset_1(B_122,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_1006])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ r2_hidden(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1045,plain,(
    ! [B_122] :
      ( m1_subset_1(B_122,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_122,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1025,c_32])).

tff(c_1058,plain,(
    ! [B_123] :
      ( m1_subset_1(B_123,'#skF_5')
      | ~ m1_subset_1(B_123,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_1045])).

tff(c_246,plain,(
    ! [B_50] :
      ( ~ m1_subset_1(B_50,'#skF_5')
      | ~ m1_subset_1(B_50,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_1098,plain,(
    ! [B_124] : ~ m1_subset_1(B_124,'#skF_6') ),
    inference(resolution,[status(thm)],[c_1058,c_246])).

tff(c_1106,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_205,c_1098])).

tff(c_1117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_1106])).

tff(c_1119,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_1674,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_3'(A_183,B_184),B_184)
      | r2_hidden('#skF_4'(A_183,B_184),A_183)
      | B_184 = A_183 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79,plain,(
    ! [A_29,B_30] : ~ r2_hidden(A_29,k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_82,plain,(
    ! [A_15] : ~ r2_hidden(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_79])).

tff(c_1752,plain,(
    ! [A_185] :
      ( r2_hidden('#skF_4'(A_185,k1_xboole_0),A_185)
      | k1_xboole_0 = A_185 ) ),
    inference(resolution,[status(thm)],[c_1674,c_82])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1791,plain,(
    ! [A_186] :
      ( ~ v1_xboole_0(A_186)
      | k1_xboole_0 = A_186 ) ),
    inference(resolution,[status(thm)],[c_1752,c_2])).

tff(c_1803,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1119,c_1791])).

tff(c_1813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1803])).

tff(c_1814,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_2060,plain,(
    ! [A_213,B_214] :
      ( r2_hidden('#skF_3'(A_213,B_214),B_214)
      | r2_hidden('#skF_4'(A_213,B_214),A_213)
      | B_214 = A_213 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2117,plain,(
    ! [A_215] :
      ( r2_hidden('#skF_4'(A_215,k1_xboole_0),A_215)
      | k1_xboole_0 = A_215 ) ),
    inference(resolution,[status(thm)],[c_2060,c_82])).

tff(c_2152,plain,(
    ! [A_216] :
      ( ~ v1_xboole_0(A_216)
      | k1_xboole_0 = A_216 ) ),
    inference(resolution,[status(thm)],[c_2117,c_2])).

tff(c_2161,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1814,c_2152])).

tff(c_2170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2161])).

tff(c_2172,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_2196,plain,(
    ! [B_225,A_226] :
      ( r2_hidden(B_225,A_226)
      | ~ m1_subset_1(B_225,A_226)
      | v1_xboole_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2224,plain,(
    ! [B_225] :
      ( ~ m1_subset_1(B_225,'#skF_5')
      | ~ m1_subset_1(B_225,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2196,c_42])).

tff(c_2257,plain,(
    ! [B_231] :
      ( ~ m1_subset_1(B_231,'#skF_5')
      | ~ m1_subset_1(B_231,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_2224])).

tff(c_2265,plain,(
    ! [B_21] :
      ( ~ m1_subset_1(B_21,'#skF_6')
      | ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_2257])).

tff(c_2271,plain,(
    ! [B_232] :
      ( ~ m1_subset_1(B_232,'#skF_6')
      | ~ v1_xboole_0(B_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2172,c_2265])).

tff(c_2281,plain,(
    ! [B_21] :
      ( ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_2271])).

tff(c_2282,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2281])).

tff(c_2173,plain,(
    ! [A_217,B_218] :
      ( r1_tarski(A_217,k3_tarski(B_218))
      | ~ r2_hidden(A_217,B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2176,plain,(
    ! [A_217,A_19] :
      ( r1_tarski(A_217,A_19)
      | ~ r2_hidden(A_217,k1_zfmisc_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2173])).

tff(c_2203,plain,(
    ! [B_225,A_19] :
      ( r1_tarski(B_225,A_19)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_2196,c_2176])).

tff(c_2228,plain,(
    ! [B_227,A_228] :
      ( r1_tarski(B_227,A_228)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_228)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2203])).

tff(c_2244,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_2228])).

tff(c_2408,plain,(
    ! [A_251,B_252] :
      ( r2_hidden('#skF_3'(A_251,B_252),B_252)
      | r2_hidden('#skF_4'(A_251,B_252),A_251)
      | B_252 = A_251 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2455,plain,(
    ! [A_253] :
      ( r2_hidden('#skF_4'(A_253,k1_xboole_0),A_253)
      | k1_xboole_0 = A_253 ) ),
    inference(resolution,[status(thm)],[c_2408,c_82])).

tff(c_2485,plain,(
    ! [A_254] :
      ( ~ v1_xboole_0(A_254)
      | k1_xboole_0 = A_254 ) ),
    inference(resolution,[status(thm)],[c_2455,c_2])).

tff(c_2496,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2172,c_2485])).

tff(c_2329,plain,(
    ! [C_243,B_244,A_245] :
      ( r2_hidden(C_243,B_244)
      | ~ r2_hidden(C_243,A_245)
      | ~ r1_tarski(A_245,B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2353,plain,(
    ! [A_248,B_249] :
      ( r2_hidden('#skF_1'(A_248),B_249)
      | ~ r1_tarski(A_248,B_249)
      | v1_xboole_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_4,c_2329])).

tff(c_2383,plain,(
    ! [A_248] :
      ( ~ r1_tarski(A_248,k1_xboole_0)
      | v1_xboole_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_2353,c_82])).

tff(c_2716,plain,(
    ! [A_265] :
      ( ~ r1_tarski(A_265,'#skF_5')
      | v1_xboole_0(A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2383])).

tff(c_2731,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2244,c_2716])).

tff(c_2744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2282,c_2731])).

tff(c_2745,plain,(
    ! [B_21] : ~ v1_xboole_0(B_21) ),
    inference(splitRight,[status(thm)],[c_2281])).

tff(c_2746,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2281])).

tff(c_2755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2745,c_2746])).

tff(c_2756,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2224])).

tff(c_2917,plain,(
    ! [A_289,B_290] :
      ( r2_hidden('#skF_3'(A_289,B_290),B_290)
      | r2_hidden('#skF_4'(A_289,B_290),A_289)
      | B_290 = A_289 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2970,plain,(
    ! [A_291] :
      ( r2_hidden('#skF_4'(A_291,k1_xboole_0),A_291)
      | k1_xboole_0 = A_291 ) ),
    inference(resolution,[status(thm)],[c_2917,c_82])).

tff(c_3000,plain,(
    ! [A_292] :
      ( ~ v1_xboole_0(A_292)
      | k1_xboole_0 = A_292 ) ),
    inference(resolution,[status(thm)],[c_2970,c_2])).

tff(c_3009,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2756,c_3000])).

tff(c_3021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3009])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.67  
% 4.01/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.68  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.01/1.68  
% 4.01/1.68  %Foreground sorts:
% 4.01/1.68  
% 4.01/1.68  
% 4.01/1.68  %Background operators:
% 4.01/1.68  
% 4.01/1.68  
% 4.01/1.68  %Foreground operators:
% 4.01/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.01/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.01/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.68  tff('#skF_5', type, '#skF_5': $i).
% 4.01/1.68  tff('#skF_6', type, '#skF_6': $i).
% 4.01/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.01/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.01/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.01/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.01/1.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.01/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.68  
% 4.01/1.70  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.01/1.70  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.01/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.01/1.70  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.01/1.70  tff(f_60, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.01/1.70  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.01/1.70  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.01/1.70  tff(f_45, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.01/1.70  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.01/1.70  tff(f_58, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.01/1.70  tff(c_44, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.01/1.70  tff(c_36, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~v1_xboole_0(B_21) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.70  tff(c_110, plain, (![B_38, A_39]: (m1_subset_1(B_38, A_39) | ~v1_xboole_0(B_38) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.70  tff(c_89, plain, (![A_35]: (v1_xboole_0(A_35) | r2_hidden('#skF_1'(A_35), A_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.70  tff(c_42, plain, (![C_24]: (~r2_hidden(C_24, '#skF_6') | ~m1_subset_1(C_24, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.01/1.70  tff(c_102, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_89, c_42])).
% 4.01/1.70  tff(c_104, plain, (~m1_subset_1('#skF_1'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_102])).
% 4.01/1.70  tff(c_118, plain, (~v1_xboole_0('#skF_1'('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_110, c_104])).
% 4.01/1.70  tff(c_119, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_118])).
% 4.01/1.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.70  tff(c_193, plain, (![B_54, A_55]: (m1_subset_1(B_54, A_55) | ~r2_hidden(B_54, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.70  tff(c_205, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_193])).
% 4.01/1.70  tff(c_155, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | ~m1_subset_1(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.70  tff(c_179, plain, (![B_50]: (~m1_subset_1(B_50, '#skF_5') | ~m1_subset_1(B_50, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_155, c_42])).
% 4.01/1.70  tff(c_257, plain, (![B_66]: (~m1_subset_1(B_66, '#skF_5') | ~m1_subset_1(B_66, '#skF_6'))), inference(splitLeft, [status(thm)], [c_179])).
% 4.01/1.70  tff(c_261, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_205, c_257])).
% 4.01/1.70  tff(c_268, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_119, c_261])).
% 4.01/1.70  tff(c_273, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_268])).
% 4.01/1.70  tff(c_274, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_273])).
% 4.01/1.70  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.01/1.70  tff(c_40, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.01/1.70  tff(c_30, plain, (![A_19]: (k3_tarski(k1_zfmisc_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.01/1.70  tff(c_120, plain, (![A_40, B_41]: (r1_tarski(A_40, k3_tarski(B_41)) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.01/1.70  tff(c_123, plain, (![A_40, A_19]: (r1_tarski(A_40, A_19) | ~r2_hidden(A_40, k1_zfmisc_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_120])).
% 4.01/1.70  tff(c_159, plain, (![B_50, A_19]: (r1_tarski(B_50, A_19) | ~m1_subset_1(B_50, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_155, c_123])).
% 4.01/1.70  tff(c_183, plain, (![B_52, A_53]: (r1_tarski(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(negUnitSimplification, [status(thm)], [c_40, c_159])).
% 4.01/1.70  tff(c_192, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_183])).
% 4.01/1.70  tff(c_34, plain, (![B_21, A_20]: (r2_hidden(B_21, A_20) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.70  tff(c_247, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.70  tff(c_1000, plain, (![B_119, B_120, A_121]: (r2_hidden(B_119, B_120) | ~r1_tarski(A_121, B_120) | ~m1_subset_1(B_119, A_121) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_34, c_247])).
% 4.01/1.70  tff(c_1006, plain, (![B_119]: (r2_hidden(B_119, '#skF_5') | ~m1_subset_1(B_119, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_192, c_1000])).
% 4.01/1.70  tff(c_1025, plain, (![B_122]: (r2_hidden(B_122, '#skF_5') | ~m1_subset_1(B_122, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_274, c_1006])).
% 4.01/1.70  tff(c_32, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~r2_hidden(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.70  tff(c_1045, plain, (![B_122]: (m1_subset_1(B_122, '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(B_122, '#skF_6'))), inference(resolution, [status(thm)], [c_1025, c_32])).
% 4.01/1.70  tff(c_1058, plain, (![B_123]: (m1_subset_1(B_123, '#skF_5') | ~m1_subset_1(B_123, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_119, c_1045])).
% 4.01/1.70  tff(c_246, plain, (![B_50]: (~m1_subset_1(B_50, '#skF_5') | ~m1_subset_1(B_50, '#skF_6'))), inference(splitLeft, [status(thm)], [c_179])).
% 4.01/1.70  tff(c_1098, plain, (![B_124]: (~m1_subset_1(B_124, '#skF_6'))), inference(resolution, [status(thm)], [c_1058, c_246])).
% 4.01/1.70  tff(c_1106, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_205, c_1098])).
% 4.01/1.70  tff(c_1117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_1106])).
% 4.01/1.70  tff(c_1119, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_273])).
% 4.01/1.70  tff(c_1674, plain, (![A_183, B_184]: (r2_hidden('#skF_3'(A_183, B_184), B_184) | r2_hidden('#skF_4'(A_183, B_184), A_183) | B_184=A_183)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.70  tff(c_24, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.01/1.70  tff(c_79, plain, (![A_29, B_30]: (~r2_hidden(A_29, k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.01/1.70  tff(c_82, plain, (![A_15]: (~r2_hidden(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_79])).
% 4.01/1.70  tff(c_1752, plain, (![A_185]: (r2_hidden('#skF_4'(A_185, k1_xboole_0), A_185) | k1_xboole_0=A_185)), inference(resolution, [status(thm)], [c_1674, c_82])).
% 4.01/1.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.70  tff(c_1791, plain, (![A_186]: (~v1_xboole_0(A_186) | k1_xboole_0=A_186)), inference(resolution, [status(thm)], [c_1752, c_2])).
% 4.01/1.70  tff(c_1803, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1119, c_1791])).
% 4.01/1.70  tff(c_1813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1803])).
% 4.01/1.70  tff(c_1814, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_179])).
% 4.01/1.70  tff(c_2060, plain, (![A_213, B_214]: (r2_hidden('#skF_3'(A_213, B_214), B_214) | r2_hidden('#skF_4'(A_213, B_214), A_213) | B_214=A_213)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.70  tff(c_2117, plain, (![A_215]: (r2_hidden('#skF_4'(A_215, k1_xboole_0), A_215) | k1_xboole_0=A_215)), inference(resolution, [status(thm)], [c_2060, c_82])).
% 4.01/1.70  tff(c_2152, plain, (![A_216]: (~v1_xboole_0(A_216) | k1_xboole_0=A_216)), inference(resolution, [status(thm)], [c_2117, c_2])).
% 4.01/1.70  tff(c_2161, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1814, c_2152])).
% 4.01/1.70  tff(c_2170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2161])).
% 4.01/1.70  tff(c_2172, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_118])).
% 4.01/1.70  tff(c_2196, plain, (![B_225, A_226]: (r2_hidden(B_225, A_226) | ~m1_subset_1(B_225, A_226) | v1_xboole_0(A_226))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.70  tff(c_2224, plain, (![B_225]: (~m1_subset_1(B_225, '#skF_5') | ~m1_subset_1(B_225, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_2196, c_42])).
% 4.01/1.70  tff(c_2257, plain, (![B_231]: (~m1_subset_1(B_231, '#skF_5') | ~m1_subset_1(B_231, '#skF_6'))), inference(splitLeft, [status(thm)], [c_2224])).
% 4.01/1.70  tff(c_2265, plain, (![B_21]: (~m1_subset_1(B_21, '#skF_6') | ~v1_xboole_0(B_21) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_2257])).
% 4.01/1.70  tff(c_2271, plain, (![B_232]: (~m1_subset_1(B_232, '#skF_6') | ~v1_xboole_0(B_232))), inference(demodulation, [status(thm), theory('equality')], [c_2172, c_2265])).
% 4.01/1.70  tff(c_2281, plain, (![B_21]: (~v1_xboole_0(B_21) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_2271])).
% 4.01/1.70  tff(c_2282, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_2281])).
% 4.01/1.70  tff(c_2173, plain, (![A_217, B_218]: (r1_tarski(A_217, k3_tarski(B_218)) | ~r2_hidden(A_217, B_218))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.01/1.70  tff(c_2176, plain, (![A_217, A_19]: (r1_tarski(A_217, A_19) | ~r2_hidden(A_217, k1_zfmisc_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2173])).
% 4.01/1.70  tff(c_2203, plain, (![B_225, A_19]: (r1_tarski(B_225, A_19) | ~m1_subset_1(B_225, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_2196, c_2176])).
% 4.01/1.70  tff(c_2228, plain, (![B_227, A_228]: (r1_tarski(B_227, A_228) | ~m1_subset_1(B_227, k1_zfmisc_1(A_228)))), inference(negUnitSimplification, [status(thm)], [c_40, c_2203])).
% 4.01/1.70  tff(c_2244, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_2228])).
% 4.01/1.70  tff(c_2408, plain, (![A_251, B_252]: (r2_hidden('#skF_3'(A_251, B_252), B_252) | r2_hidden('#skF_4'(A_251, B_252), A_251) | B_252=A_251)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.70  tff(c_2455, plain, (![A_253]: (r2_hidden('#skF_4'(A_253, k1_xboole_0), A_253) | k1_xboole_0=A_253)), inference(resolution, [status(thm)], [c_2408, c_82])).
% 4.01/1.70  tff(c_2485, plain, (![A_254]: (~v1_xboole_0(A_254) | k1_xboole_0=A_254)), inference(resolution, [status(thm)], [c_2455, c_2])).
% 4.01/1.70  tff(c_2496, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2172, c_2485])).
% 4.01/1.70  tff(c_2329, plain, (![C_243, B_244, A_245]: (r2_hidden(C_243, B_244) | ~r2_hidden(C_243, A_245) | ~r1_tarski(A_245, B_244))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.70  tff(c_2353, plain, (![A_248, B_249]: (r2_hidden('#skF_1'(A_248), B_249) | ~r1_tarski(A_248, B_249) | v1_xboole_0(A_248))), inference(resolution, [status(thm)], [c_4, c_2329])).
% 4.01/1.70  tff(c_2383, plain, (![A_248]: (~r1_tarski(A_248, k1_xboole_0) | v1_xboole_0(A_248))), inference(resolution, [status(thm)], [c_2353, c_82])).
% 4.01/1.70  tff(c_2716, plain, (![A_265]: (~r1_tarski(A_265, '#skF_5') | v1_xboole_0(A_265))), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2383])).
% 4.01/1.70  tff(c_2731, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_2244, c_2716])).
% 4.01/1.70  tff(c_2744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2282, c_2731])).
% 4.01/1.70  tff(c_2745, plain, (![B_21]: (~v1_xboole_0(B_21))), inference(splitRight, [status(thm)], [c_2281])).
% 4.01/1.70  tff(c_2746, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_2281])).
% 4.01/1.70  tff(c_2755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2745, c_2746])).
% 4.01/1.70  tff(c_2756, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_2224])).
% 4.01/1.70  tff(c_2917, plain, (![A_289, B_290]: (r2_hidden('#skF_3'(A_289, B_290), B_290) | r2_hidden('#skF_4'(A_289, B_290), A_289) | B_290=A_289)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.70  tff(c_2970, plain, (![A_291]: (r2_hidden('#skF_4'(A_291, k1_xboole_0), A_291) | k1_xboole_0=A_291)), inference(resolution, [status(thm)], [c_2917, c_82])).
% 4.01/1.70  tff(c_3000, plain, (![A_292]: (~v1_xboole_0(A_292) | k1_xboole_0=A_292)), inference(resolution, [status(thm)], [c_2970, c_2])).
% 4.01/1.70  tff(c_3009, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2756, c_3000])).
% 4.01/1.70  tff(c_3021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_3009])).
% 4.01/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.70  
% 4.01/1.70  Inference rules
% 4.01/1.70  ----------------------
% 4.01/1.70  #Ref     : 0
% 4.01/1.70  #Sup     : 599
% 4.01/1.70  #Fact    : 0
% 4.01/1.70  #Define  : 0
% 4.01/1.70  #Split   : 7
% 4.01/1.70  #Chain   : 0
% 4.01/1.70  #Close   : 0
% 4.01/1.70  
% 4.01/1.70  Ordering : KBO
% 4.01/1.70  
% 4.01/1.70  Simplification rules
% 4.01/1.70  ----------------------
% 4.01/1.70  #Subsume      : 100
% 4.01/1.70  #Demod        : 135
% 4.01/1.70  #Tautology    : 161
% 4.01/1.70  #SimpNegUnit  : 75
% 4.01/1.70  #BackRed      : 20
% 4.01/1.70  
% 4.01/1.70  #Partial instantiations: 0
% 4.01/1.70  #Strategies tried      : 1
% 4.01/1.70  
% 4.01/1.70  Timing (in seconds)
% 4.01/1.70  ----------------------
% 4.01/1.70  Preprocessing        : 0.30
% 4.01/1.70  Parsing              : 0.15
% 4.01/1.70  CNF conversion       : 0.02
% 4.01/1.70  Main loop            : 0.62
% 4.01/1.70  Inferencing          : 0.24
% 4.01/1.70  Reduction            : 0.17
% 4.01/1.70  Demodulation         : 0.10
% 4.01/1.70  BG Simplification    : 0.03
% 4.01/1.70  Subsumption          : 0.12
% 4.01/1.70  Abstraction          : 0.03
% 4.01/1.70  MUC search           : 0.00
% 4.01/1.70  Cooper               : 0.00
% 4.01/1.70  Total                : 0.96
% 4.01/1.70  Index Insertion      : 0.00
% 4.01/1.70  Index Deletion       : 0.00
% 4.01/1.70  Index Matching       : 0.00
% 4.01/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
