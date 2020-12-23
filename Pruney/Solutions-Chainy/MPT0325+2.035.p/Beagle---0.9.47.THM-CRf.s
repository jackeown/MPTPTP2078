%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:25 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 761 expanded)
%              Number of leaves         :   32 ( 263 expanded)
%              Depth                    :   20
%              Number of atoms          :  188 (1396 expanded)
%              Number of equality atoms :   60 ( 506 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_10','#skF_12')
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_91,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_227,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( r2_hidden(k4_tarski(A_91,B_92),k2_zfmisc_1(C_93,D_94))
      | ~ r2_hidden(B_92,D_94)
      | ~ r2_hidden(A_91,C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2222,plain,(
    ! [A_285,D_281,C_283,B_284,B_282] :
      ( r2_hidden(k4_tarski(A_285,B_282),B_284)
      | ~ r1_tarski(k2_zfmisc_1(C_283,D_281),B_284)
      | ~ r2_hidden(B_282,D_281)
      | ~ r2_hidden(A_285,C_283) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_2458,plain,(
    ! [A_295,B_296] :
      ( r2_hidden(k4_tarski(A_295,B_296),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_296,'#skF_10')
      | ~ r2_hidden(A_295,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_58,c_2222])).

tff(c_46,plain,(
    ! [A_49,C_51,B_50,D_52] :
      ( r2_hidden(A_49,C_51)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2481,plain,(
    ! [A_295,B_296] :
      ( r2_hidden(A_295,'#skF_11')
      | ~ r2_hidden(B_296,'#skF_10')
      | ~ r2_hidden(A_295,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2458,c_46])).

tff(c_2651,plain,(
    ! [B_304] : ~ r2_hidden(B_304,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2481])).

tff(c_2721,plain,(
    ! [B_305] : r1_tarski('#skF_10',B_305) ),
    inference(resolution,[status(thm)],[c_6,c_2651])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_776,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden('#skF_5'(A_159,B_160,C_161),B_160)
      | r2_hidden('#skF_6'(A_159,B_160,C_161),C_161)
      | k2_zfmisc_1(A_159,B_160) = C_161 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_92,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k3_xboole_0(A_64,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_121,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_12])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_134,plain,(
    ! [C_10] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_10])).

tff(c_138,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_134])).

tff(c_860,plain,(
    ! [A_162,B_163] :
      ( r2_hidden('#skF_5'(A_162,B_163,k1_xboole_0),B_163)
      | k2_zfmisc_1(A_162,B_163) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_776,c_138])).

tff(c_905,plain,(
    ! [A_164,B_165,A_166] :
      ( ~ r1_xboole_0(A_164,B_165)
      | k2_zfmisc_1(A_166,k3_xboole_0(A_164,B_165)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_860,c_10])).

tff(c_48,plain,(
    ! [B_54,A_53] :
      ( k1_xboole_0 = B_54
      | k1_xboole_0 = A_53
      | k2_zfmisc_1(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_981,plain,(
    ! [A_164,B_165,A_166] :
      ( k3_xboole_0(A_164,B_165) = k1_xboole_0
      | k1_xboole_0 = A_166
      | ~ r1_xboole_0(A_164,B_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_48])).

tff(c_1072,plain,(
    ! [A_170,B_171] :
      ( k3_xboole_0(A_170,B_171) = k1_xboole_0
      | ~ r1_xboole_0(A_170,B_171) ) ),
    inference(splitLeft,[status(thm)],[c_981])).

tff(c_1076,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_1072])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,(
    ! [A_64] : k4_xboole_0(A_64,k3_xboole_0(A_64,k1_xboole_0)) = k3_xboole_0(A_64,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_14])).

tff(c_1078,plain,(
    ! [A_64] : k4_xboole_0(A_64,k1_xboole_0) = k3_xboole_0(A_64,A_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_117])).

tff(c_1081,plain,(
    ! [A_64] : k3_xboole_0(A_64,A_64) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1078])).

tff(c_198,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_2'(A_81,B_82),k3_xboole_0(A_81,B_82))
      | r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1914,plain,(
    ! [A_266,B_267,B_268] :
      ( r2_hidden('#skF_2'(A_266,B_267),B_268)
      | ~ r1_tarski(k3_xboole_0(A_266,B_267),B_268)
      | r1_xboole_0(A_266,B_267) ) ),
    inference(resolution,[status(thm)],[c_198,c_2])).

tff(c_1958,plain,(
    ! [A_269,B_270] :
      ( ~ r1_tarski(k3_xboole_0(A_269,B_270),k1_xboole_0)
      | r1_xboole_0(A_269,B_270) ) ),
    inference(resolution,[status(thm)],[c_1914,c_138])).

tff(c_1972,plain,(
    ! [A_271] :
      ( ~ r1_tarski(A_271,k1_xboole_0)
      | r1_xboole_0(A_271,A_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_1958])).

tff(c_987,plain,(
    ! [A_164,B_165] :
      ( k3_xboole_0(A_164,B_165) = k1_xboole_0
      | ~ r1_xboole_0(A_164,B_165) ) ),
    inference(splitLeft,[status(thm)],[c_981])).

tff(c_2007,plain,(
    ! [A_271] :
      ( k3_xboole_0(A_271,A_271) = k1_xboole_0
      | ~ r1_tarski(A_271,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1972,c_987])).

tff(c_2025,plain,(
    ! [A_271] :
      ( k1_xboole_0 = A_271
      | ~ r1_tarski(A_271,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_2007])).

tff(c_2740,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2721,c_2025])).

tff(c_858,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_5'(A_159,B_160,k1_xboole_0),B_160)
      | k2_zfmisc_1(A_159,B_160) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_776,c_138])).

tff(c_2714,plain,(
    ! [A_159] : k2_zfmisc_1(A_159,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_858,c_2651])).

tff(c_2870,plain,(
    ! [A_159] : k2_zfmisc_1(A_159,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2740,c_2714])).

tff(c_56,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2775,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2740,c_56])).

tff(c_2874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2870,c_2775])).

tff(c_2876,plain,(
    ! [A_307] :
      ( r2_hidden(A_307,'#skF_11')
      | ~ r2_hidden(A_307,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2481])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2961,plain,(
    ! [A_312] :
      ( r1_tarski(A_312,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_312,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2876,c_4])).

tff(c_2969,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_2961])).

tff(c_2974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_91,c_2969])).

tff(c_2976,plain,(
    ! [A_313] : k1_xboole_0 = A_313 ),
    inference(splitRight,[status(thm)],[c_981])).

tff(c_3193,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2976,c_56])).

tff(c_3194,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3331,plain,(
    ! [A_1705,B_1706,C_1707,D_1708] :
      ( r2_hidden(k4_tarski(A_1705,B_1706),k2_zfmisc_1(C_1707,D_1708))
      | ~ r2_hidden(B_1706,D_1708)
      | ~ r2_hidden(A_1705,C_1707) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5694,plain,(
    ! [C_1907,B_1906,A_1905,B_1904,D_1908] :
      ( r2_hidden(k4_tarski(A_1905,B_1904),B_1906)
      | ~ r1_tarski(k2_zfmisc_1(C_1907,D_1908),B_1906)
      | ~ r2_hidden(B_1904,D_1908)
      | ~ r2_hidden(A_1905,C_1907) ) ),
    inference(resolution,[status(thm)],[c_3331,c_2])).

tff(c_5746,plain,(
    ! [A_1909,B_1910] :
      ( r2_hidden(k4_tarski(A_1909,B_1910),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_1910,'#skF_10')
      | ~ r2_hidden(A_1909,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_58,c_5694])).

tff(c_44,plain,(
    ! [B_50,D_52,A_49,C_51] :
      ( r2_hidden(B_50,D_52)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5774,plain,(
    ! [B_1910,A_1909] :
      ( r2_hidden(B_1910,'#skF_12')
      | ~ r2_hidden(B_1910,'#skF_10')
      | ~ r2_hidden(A_1909,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5746,c_44])).

tff(c_5962,plain,(
    ! [A_1919] : ~ r2_hidden(A_1919,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5774])).

tff(c_6033,plain,(
    ! [B_1920] : r1_tarski('#skF_9',B_1920) ),
    inference(resolution,[status(thm)],[c_6,c_5962])).

tff(c_3730,plain,(
    ! [A_1758,B_1759,C_1760] :
      ( r2_hidden('#skF_5'(A_1758,B_1759,C_1760),B_1759)
      | r2_hidden('#skF_6'(A_1758,B_1759,C_1760),C_1760)
      | k2_zfmisc_1(A_1758,B_1759) = C_1760 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3214,plain,(
    ! [A_1680,B_1681] : k4_xboole_0(A_1680,k4_xboole_0(A_1680,B_1681)) = k3_xboole_0(A_1680,B_1681) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3232,plain,(
    ! [A_1682] : k4_xboole_0(A_1682,A_1682) = k3_xboole_0(A_1682,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3214])).

tff(c_3242,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3232,c_12])).

tff(c_3255,plain,(
    ! [C_10] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3242,c_10])).

tff(c_3259,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3255])).

tff(c_3804,plain,(
    ! [A_1761,B_1762] :
      ( r2_hidden('#skF_5'(A_1761,B_1762,k1_xboole_0),B_1762)
      | k2_zfmisc_1(A_1761,B_1762) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3730,c_3259])).

tff(c_3844,plain,(
    ! [A_1763,B_1764,A_1765] :
      ( ~ r1_xboole_0(A_1763,B_1764)
      | k2_zfmisc_1(A_1765,k3_xboole_0(A_1763,B_1764)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3804,c_10])).

tff(c_3912,plain,(
    ! [A_1763,B_1764,A_1765] :
      ( k3_xboole_0(A_1763,B_1764) = k1_xboole_0
      | k1_xboole_0 = A_1765
      | ~ r1_xboole_0(A_1763,B_1764) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3844,c_48])).

tff(c_3993,plain,(
    ! [A_1769,B_1770] :
      ( k3_xboole_0(A_1769,B_1770) = k1_xboole_0
      | ~ r1_xboole_0(A_1769,B_1770) ) ),
    inference(splitLeft,[status(thm)],[c_3912])).

tff(c_3997,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_3993])).

tff(c_3238,plain,(
    ! [A_1682] : k4_xboole_0(A_1682,k3_xboole_0(A_1682,k1_xboole_0)) = k3_xboole_0(A_1682,A_1682) ),
    inference(superposition,[status(thm),theory(equality)],[c_3232,c_14])).

tff(c_3999,plain,(
    ! [A_1682] : k4_xboole_0(A_1682,k1_xboole_0) = k3_xboole_0(A_1682,A_1682) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3997,c_3238])).

tff(c_4002,plain,(
    ! [A_1682] : k3_xboole_0(A_1682,A_1682) = A_1682 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3999])).

tff(c_4073,plain,(
    ! [A_1772] : k3_xboole_0(A_1772,A_1772) = A_1772 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3999])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4249,plain,(
    ! [A_1786] :
      ( r2_hidden('#skF_2'(A_1786,A_1786),A_1786)
      | r1_xboole_0(A_1786,A_1786) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4073,c_8])).

tff(c_5061,plain,(
    ! [A_1874,B_1875] :
      ( r2_hidden('#skF_2'(A_1874,A_1874),B_1875)
      | ~ r1_tarski(A_1874,B_1875)
      | r1_xboole_0(A_1874,A_1874) ) ),
    inference(resolution,[status(thm)],[c_4249,c_2])).

tff(c_5128,plain,(
    ! [A_1879] :
      ( ~ r1_tarski(A_1879,k1_xboole_0)
      | r1_xboole_0(A_1879,A_1879) ) ),
    inference(resolution,[status(thm)],[c_5061,c_3259])).

tff(c_3918,plain,(
    ! [A_1763,B_1764] :
      ( k3_xboole_0(A_1763,B_1764) = k1_xboole_0
      | ~ r1_xboole_0(A_1763,B_1764) ) ),
    inference(splitLeft,[status(thm)],[c_3912])).

tff(c_5163,plain,(
    ! [A_1879] :
      ( k3_xboole_0(A_1879,A_1879) = k1_xboole_0
      | ~ r1_tarski(A_1879,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5128,c_3918])).

tff(c_5181,plain,(
    ! [A_1879] :
      ( k1_xboole_0 = A_1879
      | ~ r1_tarski(A_1879,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4002,c_5163])).

tff(c_6055,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6033,c_5181])).

tff(c_3919,plain,(
    ! [A_1766,B_1767,C_1768] :
      ( r2_hidden('#skF_4'(A_1766,B_1767,C_1768),A_1766)
      | r2_hidden('#skF_6'(A_1766,B_1767,C_1768),C_1768)
      | k2_zfmisc_1(A_1766,B_1767) = C_1768 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3991,plain,(
    ! [A_1766,B_1767] :
      ( r2_hidden('#skF_4'(A_1766,B_1767,k1_xboole_0),A_1766)
      | k2_zfmisc_1(A_1766,B_1767) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3919,c_3259])).

tff(c_6022,plain,(
    ! [B_1767] : k2_zfmisc_1('#skF_9',B_1767) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3991,c_5962])).

tff(c_6216,plain,(
    ! [B_1767] : k2_zfmisc_1('#skF_9',B_1767) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6055,c_6022])).

tff(c_6096,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6055,c_56])).

tff(c_6359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6216,c_6096])).

tff(c_6361,plain,(
    ! [B_1928] :
      ( r2_hidden(B_1928,'#skF_12')
      | ~ r2_hidden(B_1928,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_5774])).

tff(c_6431,plain,(
    ! [B_1929] :
      ( r2_hidden('#skF_1'('#skF_10',B_1929),'#skF_12')
      | r1_tarski('#skF_10',B_1929) ) ),
    inference(resolution,[status(thm)],[c_6,c_6361])).

tff(c_6440,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_6431,c_4])).

tff(c_6446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3194,c_3194,c_6440])).

tff(c_6448,plain,(
    ! [A_1930] : k1_xboole_0 = A_1930 ),
    inference(splitRight,[status(thm)],[c_3912])).

tff(c_6642,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_6448,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.52/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.10  
% 5.52/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 5.52/2.10  
% 5.52/2.10  %Foreground sorts:
% 5.52/2.10  
% 5.52/2.10  
% 5.52/2.10  %Background operators:
% 5.52/2.10  
% 5.52/2.10  
% 5.52/2.10  %Foreground operators:
% 5.52/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.52/2.10  tff('#skF_11', type, '#skF_11': $i).
% 5.52/2.10  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.52/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.52/2.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.52/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.52/2.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.52/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.52/2.10  tff('#skF_10', type, '#skF_10': $i).
% 5.52/2.10  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.52/2.10  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.52/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.52/2.10  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 5.52/2.10  tff('#skF_9', type, '#skF_9': $i).
% 5.52/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.52/2.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.52/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.52/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.52/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.52/2.10  tff('#skF_12', type, '#skF_12': $i).
% 5.52/2.10  
% 5.52/2.12  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.52/2.12  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.52/2.12  tff(f_70, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.52/2.12  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.52/2.12  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.52/2.12  tff(f_64, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.52/2.12  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.52/2.12  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.52/2.12  tff(f_76, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.52/2.12  tff(c_54, plain, (~r1_tarski('#skF_10', '#skF_12') | ~r1_tarski('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.52/2.12  tff(c_91, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_54])).
% 5.52/2.12  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.52/2.12  tff(c_58, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.52/2.12  tff(c_227, plain, (![A_91, B_92, C_93, D_94]: (r2_hidden(k4_tarski(A_91, B_92), k2_zfmisc_1(C_93, D_94)) | ~r2_hidden(B_92, D_94) | ~r2_hidden(A_91, C_93))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.52/2.12  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.52/2.12  tff(c_2222, plain, (![A_285, D_281, C_283, B_284, B_282]: (r2_hidden(k4_tarski(A_285, B_282), B_284) | ~r1_tarski(k2_zfmisc_1(C_283, D_281), B_284) | ~r2_hidden(B_282, D_281) | ~r2_hidden(A_285, C_283))), inference(resolution, [status(thm)], [c_227, c_2])).
% 5.52/2.12  tff(c_2458, plain, (![A_295, B_296]: (r2_hidden(k4_tarski(A_295, B_296), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_296, '#skF_10') | ~r2_hidden(A_295, '#skF_9'))), inference(resolution, [status(thm)], [c_58, c_2222])).
% 5.52/2.12  tff(c_46, plain, (![A_49, C_51, B_50, D_52]: (r2_hidden(A_49, C_51) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.52/2.12  tff(c_2481, plain, (![A_295, B_296]: (r2_hidden(A_295, '#skF_11') | ~r2_hidden(B_296, '#skF_10') | ~r2_hidden(A_295, '#skF_9'))), inference(resolution, [status(thm)], [c_2458, c_46])).
% 5.52/2.12  tff(c_2651, plain, (![B_304]: (~r2_hidden(B_304, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2481])).
% 5.52/2.12  tff(c_2721, plain, (![B_305]: (r1_tarski('#skF_10', B_305))), inference(resolution, [status(thm)], [c_6, c_2651])).
% 5.52/2.12  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.52/2.12  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.52/2.12  tff(c_776, plain, (![A_159, B_160, C_161]: (r2_hidden('#skF_5'(A_159, B_160, C_161), B_160) | r2_hidden('#skF_6'(A_159, B_160, C_161), C_161) | k2_zfmisc_1(A_159, B_160)=C_161)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.52/2.12  tff(c_92, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.52/2.12  tff(c_111, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k3_xboole_0(A_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_92])).
% 5.52/2.12  tff(c_121, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_111, c_12])).
% 5.52/2.12  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.52/2.12  tff(c_134, plain, (![C_10]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_121, c_10])).
% 5.52/2.12  tff(c_138, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_134])).
% 5.52/2.12  tff(c_860, plain, (![A_162, B_163]: (r2_hidden('#skF_5'(A_162, B_163, k1_xboole_0), B_163) | k2_zfmisc_1(A_162, B_163)=k1_xboole_0)), inference(resolution, [status(thm)], [c_776, c_138])).
% 5.52/2.12  tff(c_905, plain, (![A_164, B_165, A_166]: (~r1_xboole_0(A_164, B_165) | k2_zfmisc_1(A_166, k3_xboole_0(A_164, B_165))=k1_xboole_0)), inference(resolution, [status(thm)], [c_860, c_10])).
% 5.52/2.12  tff(c_48, plain, (![B_54, A_53]: (k1_xboole_0=B_54 | k1_xboole_0=A_53 | k2_zfmisc_1(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.52/2.12  tff(c_981, plain, (![A_164, B_165, A_166]: (k3_xboole_0(A_164, B_165)=k1_xboole_0 | k1_xboole_0=A_166 | ~r1_xboole_0(A_164, B_165))), inference(superposition, [status(thm), theory('equality')], [c_905, c_48])).
% 5.52/2.12  tff(c_1072, plain, (![A_170, B_171]: (k3_xboole_0(A_170, B_171)=k1_xboole_0 | ~r1_xboole_0(A_170, B_171))), inference(splitLeft, [status(thm)], [c_981])).
% 5.52/2.12  tff(c_1076, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1072])).
% 5.52/2.12  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.52/2.12  tff(c_117, plain, (![A_64]: (k4_xboole_0(A_64, k3_xboole_0(A_64, k1_xboole_0))=k3_xboole_0(A_64, A_64))), inference(superposition, [status(thm), theory('equality')], [c_111, c_14])).
% 5.52/2.12  tff(c_1078, plain, (![A_64]: (k4_xboole_0(A_64, k1_xboole_0)=k3_xboole_0(A_64, A_64))), inference(demodulation, [status(thm), theory('equality')], [c_1076, c_117])).
% 5.52/2.12  tff(c_1081, plain, (![A_64]: (k3_xboole_0(A_64, A_64)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1078])).
% 5.52/2.12  tff(c_198, plain, (![A_81, B_82]: (r2_hidden('#skF_2'(A_81, B_82), k3_xboole_0(A_81, B_82)) | r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.52/2.12  tff(c_1914, plain, (![A_266, B_267, B_268]: (r2_hidden('#skF_2'(A_266, B_267), B_268) | ~r1_tarski(k3_xboole_0(A_266, B_267), B_268) | r1_xboole_0(A_266, B_267))), inference(resolution, [status(thm)], [c_198, c_2])).
% 5.52/2.12  tff(c_1958, plain, (![A_269, B_270]: (~r1_tarski(k3_xboole_0(A_269, B_270), k1_xboole_0) | r1_xboole_0(A_269, B_270))), inference(resolution, [status(thm)], [c_1914, c_138])).
% 5.52/2.12  tff(c_1972, plain, (![A_271]: (~r1_tarski(A_271, k1_xboole_0) | r1_xboole_0(A_271, A_271))), inference(superposition, [status(thm), theory('equality')], [c_1081, c_1958])).
% 5.52/2.12  tff(c_987, plain, (![A_164, B_165]: (k3_xboole_0(A_164, B_165)=k1_xboole_0 | ~r1_xboole_0(A_164, B_165))), inference(splitLeft, [status(thm)], [c_981])).
% 5.52/2.12  tff(c_2007, plain, (![A_271]: (k3_xboole_0(A_271, A_271)=k1_xboole_0 | ~r1_tarski(A_271, k1_xboole_0))), inference(resolution, [status(thm)], [c_1972, c_987])).
% 5.52/2.12  tff(c_2025, plain, (![A_271]: (k1_xboole_0=A_271 | ~r1_tarski(A_271, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_2007])).
% 5.52/2.12  tff(c_2740, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_2721, c_2025])).
% 5.52/2.12  tff(c_858, plain, (![A_159, B_160]: (r2_hidden('#skF_5'(A_159, B_160, k1_xboole_0), B_160) | k2_zfmisc_1(A_159, B_160)=k1_xboole_0)), inference(resolution, [status(thm)], [c_776, c_138])).
% 5.52/2.12  tff(c_2714, plain, (![A_159]: (k2_zfmisc_1(A_159, '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_858, c_2651])).
% 5.52/2.12  tff(c_2870, plain, (![A_159]: (k2_zfmisc_1(A_159, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2740, c_2714])).
% 5.52/2.12  tff(c_56, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.52/2.12  tff(c_2775, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2740, c_56])).
% 5.52/2.12  tff(c_2874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2870, c_2775])).
% 5.52/2.12  tff(c_2876, plain, (![A_307]: (r2_hidden(A_307, '#skF_11') | ~r2_hidden(A_307, '#skF_9'))), inference(splitRight, [status(thm)], [c_2481])).
% 5.52/2.12  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.52/2.12  tff(c_2961, plain, (![A_312]: (r1_tarski(A_312, '#skF_11') | ~r2_hidden('#skF_1'(A_312, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_2876, c_4])).
% 5.52/2.12  tff(c_2969, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_2961])).
% 5.52/2.12  tff(c_2974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_91, c_2969])).
% 5.52/2.12  tff(c_2976, plain, (![A_313]: (k1_xboole_0=A_313)), inference(splitRight, [status(thm)], [c_981])).
% 5.52/2.12  tff(c_3193, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2976, c_56])).
% 5.52/2.12  tff(c_3194, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_54])).
% 5.52/2.12  tff(c_3331, plain, (![A_1705, B_1706, C_1707, D_1708]: (r2_hidden(k4_tarski(A_1705, B_1706), k2_zfmisc_1(C_1707, D_1708)) | ~r2_hidden(B_1706, D_1708) | ~r2_hidden(A_1705, C_1707))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.52/2.12  tff(c_5694, plain, (![C_1907, B_1906, A_1905, B_1904, D_1908]: (r2_hidden(k4_tarski(A_1905, B_1904), B_1906) | ~r1_tarski(k2_zfmisc_1(C_1907, D_1908), B_1906) | ~r2_hidden(B_1904, D_1908) | ~r2_hidden(A_1905, C_1907))), inference(resolution, [status(thm)], [c_3331, c_2])).
% 5.52/2.12  tff(c_5746, plain, (![A_1909, B_1910]: (r2_hidden(k4_tarski(A_1909, B_1910), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_1910, '#skF_10') | ~r2_hidden(A_1909, '#skF_9'))), inference(resolution, [status(thm)], [c_58, c_5694])).
% 5.52/2.12  tff(c_44, plain, (![B_50, D_52, A_49, C_51]: (r2_hidden(B_50, D_52) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.52/2.12  tff(c_5774, plain, (![B_1910, A_1909]: (r2_hidden(B_1910, '#skF_12') | ~r2_hidden(B_1910, '#skF_10') | ~r2_hidden(A_1909, '#skF_9'))), inference(resolution, [status(thm)], [c_5746, c_44])).
% 5.52/2.12  tff(c_5962, plain, (![A_1919]: (~r2_hidden(A_1919, '#skF_9'))), inference(splitLeft, [status(thm)], [c_5774])).
% 5.52/2.12  tff(c_6033, plain, (![B_1920]: (r1_tarski('#skF_9', B_1920))), inference(resolution, [status(thm)], [c_6, c_5962])).
% 5.52/2.12  tff(c_3730, plain, (![A_1758, B_1759, C_1760]: (r2_hidden('#skF_5'(A_1758, B_1759, C_1760), B_1759) | r2_hidden('#skF_6'(A_1758, B_1759, C_1760), C_1760) | k2_zfmisc_1(A_1758, B_1759)=C_1760)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.52/2.12  tff(c_3214, plain, (![A_1680, B_1681]: (k4_xboole_0(A_1680, k4_xboole_0(A_1680, B_1681))=k3_xboole_0(A_1680, B_1681))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.52/2.12  tff(c_3232, plain, (![A_1682]: (k4_xboole_0(A_1682, A_1682)=k3_xboole_0(A_1682, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3214])).
% 5.52/2.12  tff(c_3242, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3232, c_12])).
% 5.52/2.12  tff(c_3255, plain, (![C_10]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3242, c_10])).
% 5.52/2.12  tff(c_3259, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3255])).
% 5.52/2.12  tff(c_3804, plain, (![A_1761, B_1762]: (r2_hidden('#skF_5'(A_1761, B_1762, k1_xboole_0), B_1762) | k2_zfmisc_1(A_1761, B_1762)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3730, c_3259])).
% 5.52/2.12  tff(c_3844, plain, (![A_1763, B_1764, A_1765]: (~r1_xboole_0(A_1763, B_1764) | k2_zfmisc_1(A_1765, k3_xboole_0(A_1763, B_1764))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3804, c_10])).
% 5.52/2.12  tff(c_3912, plain, (![A_1763, B_1764, A_1765]: (k3_xboole_0(A_1763, B_1764)=k1_xboole_0 | k1_xboole_0=A_1765 | ~r1_xboole_0(A_1763, B_1764))), inference(superposition, [status(thm), theory('equality')], [c_3844, c_48])).
% 5.52/2.12  tff(c_3993, plain, (![A_1769, B_1770]: (k3_xboole_0(A_1769, B_1770)=k1_xboole_0 | ~r1_xboole_0(A_1769, B_1770))), inference(splitLeft, [status(thm)], [c_3912])).
% 5.52/2.12  tff(c_3997, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_3993])).
% 5.52/2.12  tff(c_3238, plain, (![A_1682]: (k4_xboole_0(A_1682, k3_xboole_0(A_1682, k1_xboole_0))=k3_xboole_0(A_1682, A_1682))), inference(superposition, [status(thm), theory('equality')], [c_3232, c_14])).
% 5.52/2.12  tff(c_3999, plain, (![A_1682]: (k4_xboole_0(A_1682, k1_xboole_0)=k3_xboole_0(A_1682, A_1682))), inference(demodulation, [status(thm), theory('equality')], [c_3997, c_3238])).
% 5.52/2.12  tff(c_4002, plain, (![A_1682]: (k3_xboole_0(A_1682, A_1682)=A_1682)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3999])).
% 5.52/2.12  tff(c_4073, plain, (![A_1772]: (k3_xboole_0(A_1772, A_1772)=A_1772)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3999])).
% 5.52/2.12  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.52/2.12  tff(c_4249, plain, (![A_1786]: (r2_hidden('#skF_2'(A_1786, A_1786), A_1786) | r1_xboole_0(A_1786, A_1786))), inference(superposition, [status(thm), theory('equality')], [c_4073, c_8])).
% 5.52/2.12  tff(c_5061, plain, (![A_1874, B_1875]: (r2_hidden('#skF_2'(A_1874, A_1874), B_1875) | ~r1_tarski(A_1874, B_1875) | r1_xboole_0(A_1874, A_1874))), inference(resolution, [status(thm)], [c_4249, c_2])).
% 5.52/2.12  tff(c_5128, plain, (![A_1879]: (~r1_tarski(A_1879, k1_xboole_0) | r1_xboole_0(A_1879, A_1879))), inference(resolution, [status(thm)], [c_5061, c_3259])).
% 5.52/2.12  tff(c_3918, plain, (![A_1763, B_1764]: (k3_xboole_0(A_1763, B_1764)=k1_xboole_0 | ~r1_xboole_0(A_1763, B_1764))), inference(splitLeft, [status(thm)], [c_3912])).
% 5.52/2.12  tff(c_5163, plain, (![A_1879]: (k3_xboole_0(A_1879, A_1879)=k1_xboole_0 | ~r1_tarski(A_1879, k1_xboole_0))), inference(resolution, [status(thm)], [c_5128, c_3918])).
% 5.52/2.12  tff(c_5181, plain, (![A_1879]: (k1_xboole_0=A_1879 | ~r1_tarski(A_1879, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4002, c_5163])).
% 5.52/2.12  tff(c_6055, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6033, c_5181])).
% 5.52/2.12  tff(c_3919, plain, (![A_1766, B_1767, C_1768]: (r2_hidden('#skF_4'(A_1766, B_1767, C_1768), A_1766) | r2_hidden('#skF_6'(A_1766, B_1767, C_1768), C_1768) | k2_zfmisc_1(A_1766, B_1767)=C_1768)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.52/2.12  tff(c_3991, plain, (![A_1766, B_1767]: (r2_hidden('#skF_4'(A_1766, B_1767, k1_xboole_0), A_1766) | k2_zfmisc_1(A_1766, B_1767)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3919, c_3259])).
% 5.52/2.12  tff(c_6022, plain, (![B_1767]: (k2_zfmisc_1('#skF_9', B_1767)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3991, c_5962])).
% 5.52/2.12  tff(c_6216, plain, (![B_1767]: (k2_zfmisc_1('#skF_9', B_1767)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6055, c_6022])).
% 5.52/2.12  tff(c_6096, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6055, c_56])).
% 5.52/2.12  tff(c_6359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6216, c_6096])).
% 5.52/2.12  tff(c_6361, plain, (![B_1928]: (r2_hidden(B_1928, '#skF_12') | ~r2_hidden(B_1928, '#skF_10'))), inference(splitRight, [status(thm)], [c_5774])).
% 5.52/2.12  tff(c_6431, plain, (![B_1929]: (r2_hidden('#skF_1'('#skF_10', B_1929), '#skF_12') | r1_tarski('#skF_10', B_1929))), inference(resolution, [status(thm)], [c_6, c_6361])).
% 5.52/2.12  tff(c_6440, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_6431, c_4])).
% 5.52/2.12  tff(c_6446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3194, c_3194, c_6440])).
% 5.52/2.12  tff(c_6448, plain, (![A_1930]: (k1_xboole_0=A_1930)), inference(splitRight, [status(thm)], [c_3912])).
% 5.52/2.12  tff(c_6642, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_6448, c_56])).
% 5.52/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.12  
% 5.52/2.12  Inference rules
% 5.52/2.12  ----------------------
% 5.52/2.12  #Ref     : 0
% 5.52/2.12  #Sup     : 1585
% 5.52/2.12  #Fact    : 0
% 5.52/2.12  #Define  : 0
% 5.52/2.12  #Split   : 8
% 5.52/2.12  #Chain   : 0
% 5.52/2.12  #Close   : 0
% 5.52/2.12  
% 5.52/2.12  Ordering : KBO
% 5.52/2.12  
% 5.52/2.12  Simplification rules
% 5.52/2.12  ----------------------
% 5.52/2.12  #Subsume      : 520
% 5.52/2.12  #Demod        : 638
% 5.52/2.12  #Tautology    : 385
% 5.52/2.12  #SimpNegUnit  : 38
% 5.52/2.12  #BackRed      : 79
% 5.52/2.12  
% 5.52/2.12  #Partial instantiations: 316
% 5.52/2.12  #Strategies tried      : 1
% 5.52/2.12  
% 5.52/2.12  Timing (in seconds)
% 5.52/2.12  ----------------------
% 5.71/2.12  Preprocessing        : 0.31
% 5.71/2.12  Parsing              : 0.17
% 5.71/2.12  CNF conversion       : 0.03
% 5.71/2.12  Main loop            : 0.98
% 5.71/2.12  Inferencing          : 0.38
% 5.71/2.12  Reduction            : 0.29
% 5.71/2.12  Demodulation         : 0.21
% 5.71/2.12  BG Simplification    : 0.04
% 5.71/2.12  Subsumption          : 0.20
% 5.71/2.12  Abstraction          : 0.05
% 5.71/2.12  MUC search           : 0.00
% 5.71/2.12  Cooper               : 0.00
% 5.71/2.12  Total                : 1.34
% 5.71/2.12  Index Insertion      : 0.00
% 5.71/2.12  Index Deletion       : 0.00
% 5.71/2.12  Index Matching       : 0.00
% 5.71/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
