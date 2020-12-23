%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:44 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  215 (1028 expanded)
%              Number of leaves         :   34 ( 313 expanded)
%              Depth                    :   12
%              Number of atoms          :  264 (1947 expanded)
%              Number of equality atoms :  122 (1355 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_58,B_59] : r1_tarski(k3_xboole_0(A_58,B_59),A_58) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    ! [B_59] : k3_xboole_0(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_12])).

tff(c_795,plain,(
    ! [A_181,B_182,C_183] :
      ( ~ r1_xboole_0(A_181,B_182)
      | ~ r2_hidden(C_183,k3_xboole_0(A_181,B_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_802,plain,(
    ! [B_59,C_183] :
      ( ~ r1_xboole_0(k1_xboole_0,B_59)
      | ~ r2_hidden(C_183,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_795])).

tff(c_805,plain,(
    ! [C_183] : ~ r2_hidden(C_183,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_100,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_109,plain,(
    ! [B_59] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_100])).

tff(c_113,plain,(
    ! [B_64] : k4_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_109])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,(
    ! [B_64] : r1_xboole_0(k1_xboole_0,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_123,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,(
    ! [B_59,C_67] :
      ( ~ r1_xboole_0(k1_xboole_0,B_59)
      | ~ r2_hidden(C_67,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_123])).

tff(c_134,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_130])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_95,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_234,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( r2_hidden(k4_tarski(A_88,B_89),k2_zfmisc_1(C_90,D_91))
      | ~ r2_hidden(B_89,D_91)
      | ~ r2_hidden(A_88,C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_243,plain,(
    ! [A_88,B_89] :
      ( r2_hidden(k4_tarski(A_88,B_89),k1_xboole_0)
      | ~ r2_hidden(B_89,'#skF_12')
      | ~ r2_hidden(A_88,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_234])).

tff(c_246,plain,(
    ! [B_89,A_88] :
      ( ~ r2_hidden(B_89,'#skF_12')
      | ~ r2_hidden(A_88,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_243])).

tff(c_248,plain,(
    ! [A_92] : ~ r2_hidden(A_92,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_252,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_6,c_248])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_252])).

tff(c_258,plain,(
    ! [B_93] : ~ r2_hidden(B_93,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_262,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_262])).

tff(c_267,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_269,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_274,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_6])).

tff(c_480,plain,(
    ! [A_133,B_134,D_135] :
      ( r2_hidden('#skF_8'(A_133,B_134,k2_zfmisc_1(A_133,B_134),D_135),B_134)
      | ~ r2_hidden(D_135,k2_zfmisc_1(A_133,B_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_277,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_10') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_14])).

tff(c_275,plain,(
    ! [B_59] : k3_xboole_0('#skF_10',B_59) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_269,c_75])).

tff(c_316,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_325,plain,(
    ! [B_59] : k5_xboole_0('#skF_10','#skF_10') = k4_xboole_0('#skF_10',B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_316])).

tff(c_338,plain,(
    ! [B_103] : k4_xboole_0('#skF_10',B_103) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_325])).

tff(c_343,plain,(
    ! [B_103] : r1_xboole_0('#skF_10',B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_16])).

tff(c_329,plain,(
    ! [A_100,B_101,C_102] :
      ( ~ r1_xboole_0(A_100,B_101)
      | ~ r2_hidden(C_102,k3_xboole_0(A_100,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_336,plain,(
    ! [B_59,C_102] :
      ( ~ r1_xboole_0('#skF_10',B_59)
      | ~ r2_hidden(C_102,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_329])).

tff(c_350,plain,(
    ! [C_102] : ~ r2_hidden(C_102,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_336])).

tff(c_524,plain,(
    ! [D_137,A_138] : ~ r2_hidden(D_137,k2_zfmisc_1(A_138,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_480,c_350])).

tff(c_547,plain,(
    ! [A_138] : k2_zfmisc_1(A_138,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_274,c_524])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_94,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_270,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_94])).

tff(c_551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_270])).

tff(c_552,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_559,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_6])).

tff(c_738,plain,(
    ! [A_173,B_174,D_175] :
      ( r2_hidden('#skF_7'(A_173,B_174,k2_zfmisc_1(A_173,B_174),D_175),A_173)
      | ~ r2_hidden(D_175,k2_zfmisc_1(A_173,B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_562,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_9') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_14])).

tff(c_560,plain,(
    ! [B_59] : k3_xboole_0('#skF_9',B_59) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_552,c_75])).

tff(c_601,plain,(
    ! [A_143,B_144] : k5_xboole_0(A_143,k3_xboole_0(A_143,B_144)) = k4_xboole_0(A_143,B_144) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_610,plain,(
    ! [B_59] : k5_xboole_0('#skF_9','#skF_9') = k4_xboole_0('#skF_9',B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_601])).

tff(c_614,plain,(
    ! [B_145] : k4_xboole_0('#skF_9',B_145) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_610])).

tff(c_619,plain,(
    ! [B_145] : r1_xboole_0('#skF_9',B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_16])).

tff(c_625,plain,(
    ! [A_147,B_148,C_149] :
      ( ~ r1_xboole_0(A_147,B_148)
      | ~ r2_hidden(C_149,k3_xboole_0(A_147,B_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_632,plain,(
    ! [B_59,C_149] :
      ( ~ r1_xboole_0('#skF_9',B_59)
      | ~ r2_hidden(C_149,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_625])).

tff(c_635,plain,(
    ! [C_149] : ~ r2_hidden(C_149,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_632])).

tff(c_760,plain,(
    ! [D_179,B_180] : ~ r2_hidden(D_179,k2_zfmisc_1('#skF_9',B_180)) ),
    inference(resolution,[status(thm)],[c_738,c_635])).

tff(c_780,plain,(
    ! [B_180] : k2_zfmisc_1('#skF_9',B_180) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_559,c_760])).

tff(c_555,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_94])).

tff(c_784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_555])).

tff(c_786,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_935,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( r2_hidden(k4_tarski(A_207,B_208),k2_zfmisc_1(C_209,D_210))
      | ~ r2_hidden(B_208,D_210)
      | ~ r2_hidden(A_207,C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_944,plain,(
    ! [A_207,B_208] :
      ( r2_hidden(k4_tarski(A_207,B_208),k1_xboole_0)
      | ~ r2_hidden(B_208,'#skF_10')
      | ~ r2_hidden(A_207,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_935])).

tff(c_950,plain,(
    ! [B_208,A_207] :
      ( ~ r2_hidden(B_208,'#skF_10')
      | ~ r2_hidden(A_207,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_805,c_944])).

tff(c_953,plain,(
    ! [A_211] : ~ r2_hidden(A_211,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_950])).

tff(c_958,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_953])).

tff(c_968,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_92])).

tff(c_1345,plain,(
    ! [A_245] :
      ( r2_hidden('#skF_2'(A_245),A_245)
      | A_245 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_6])).

tff(c_967,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_93])).

tff(c_1195,plain,(
    ! [A_234] :
      ( r2_hidden('#skF_2'(A_234),A_234)
      | A_234 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_6])).

tff(c_785,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_947,plain,(
    ! [A_207,B_208] :
      ( r2_hidden(k4_tarski(A_207,B_208),k1_xboole_0)
      | ~ r2_hidden(B_208,'#skF_12')
      | ~ r2_hidden(A_207,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_935])).

tff(c_951,plain,(
    ! [B_208,A_207] :
      ( ~ r2_hidden(B_208,'#skF_12')
      | ~ r2_hidden(A_207,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_805,c_947])).

tff(c_1149,plain,(
    ! [A_207] : ~ r2_hidden(A_207,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_1207,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1195,c_1149])).

tff(c_1229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_967,c_1207])).

tff(c_1230,plain,(
    ! [B_208] : ~ r2_hidden(B_208,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_1357,plain,(
    '#skF_9' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1345,c_1230])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_1357])).

tff(c_1392,plain,(
    ! [B_247] : ~ r2_hidden(B_247,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_1397,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6,c_1392])).

tff(c_1407,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_92])).

tff(c_1635,plain,(
    ! [A_270] :
      ( r2_hidden('#skF_2'(A_270),A_270)
      | A_270 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_6])).

tff(c_1382,plain,(
    ! [A_246] : ~ r2_hidden(A_246,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_1386,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_6,c_1382])).

tff(c_1390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1386])).

tff(c_1391,plain,(
    ! [B_208] : ~ r2_hidden(B_208,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_1655,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1635,c_1391])).

tff(c_1671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1407,c_1655])).

tff(c_1672,plain,(
    ! [B_59] : ~ r1_xboole_0(k1_xboole_0,B_59) ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_1694,plain,(
    ! [A_276,B_277] : k5_xboole_0(A_276,k3_xboole_0(A_276,B_277)) = k4_xboole_0(A_276,B_277) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1706,plain,(
    ! [B_59] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_1694])).

tff(c_1718,plain,(
    ! [B_279] : k4_xboole_0(k1_xboole_0,B_279) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1706])).

tff(c_1726,plain,(
    ! [B_279] : r1_xboole_0(k1_xboole_0,B_279) ),
    inference(superposition,[status(thm),theory(equality)],[c_1718,c_16])).

tff(c_1732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1672,c_1726])).

tff(c_1734,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1733,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1747,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_1734,c_1733])).

tff(c_1748,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1747])).

tff(c_1737,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_6])).

tff(c_1797,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1748,c_1737])).

tff(c_2050,plain,(
    ! [A_327,B_328,D_329] :
      ( r2_hidden('#skF_8'(A_327,B_328,k2_zfmisc_1(A_327,B_328),D_329),B_328)
      | ~ r2_hidden(D_329,k2_zfmisc_1(A_327,B_328)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1738,plain,(
    ! [B_59] : k3_xboole_0('#skF_11',B_59) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_1734,c_75])).

tff(c_1772,plain,(
    ! [B_59] : k3_xboole_0('#skF_10',B_59) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1748,c_1748,c_1738])).

tff(c_1801,plain,(
    ! [A_284,B_285,C_286] :
      ( ~ r1_xboole_0(A_284,B_285)
      | ~ r2_hidden(C_286,k3_xboole_0(A_284,B_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1808,plain,(
    ! [B_59,C_286] :
      ( ~ r1_xboole_0('#skF_10',B_59)
      | ~ r2_hidden(C_286,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1772,c_1801])).

tff(c_1810,plain,(
    ! [C_286] : ~ r2_hidden(C_286,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1808])).

tff(c_2073,plain,(
    ! [D_330,A_331] : ~ r2_hidden(D_330,k2_zfmisc_1(A_331,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_2050,c_1810])).

tff(c_2099,plain,(
    ! [A_331] : k2_zfmisc_1(A_331,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1797,c_2073])).

tff(c_1751,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1748,c_1734])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1771,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1751,c_1748,c_1751,c_52])).

tff(c_2103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2099,c_1771])).

tff(c_2104,plain,(
    ! [B_59] : ~ r1_xboole_0('#skF_10',B_59) ),
    inference(splitRight,[status(thm)],[c_1808])).

tff(c_1740,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_11') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1734,c_14])).

tff(c_1760,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_10') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1748,c_1740])).

tff(c_2106,plain,(
    ! [A_333,B_334] : k5_xboole_0(A_333,k3_xboole_0(A_333,B_334)) = k4_xboole_0(A_333,B_334) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2115,plain,(
    ! [B_59] : k5_xboole_0('#skF_10','#skF_10') = k4_xboole_0('#skF_10',B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_1772,c_2106])).

tff(c_2119,plain,(
    ! [B_335] : k4_xboole_0('#skF_10',B_335) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1760,c_2115])).

tff(c_2124,plain,(
    ! [B_335] : r1_xboole_0('#skF_10',B_335) ),
    inference(superposition,[status(thm),theory(equality)],[c_2119,c_16])).

tff(c_2129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2104,c_2124])).

tff(c_2130,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1747])).

tff(c_2181,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_1737])).

tff(c_2374,plain,(
    ! [A_376,B_377,D_378] :
      ( r2_hidden('#skF_7'(A_376,B_377,k2_zfmisc_1(A_376,B_377),D_378),A_376)
      | ~ r2_hidden(D_378,k2_zfmisc_1(A_376,B_377)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2144,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_9') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_1740])).

tff(c_2154,plain,(
    ! [B_59] : k3_xboole_0('#skF_9',B_59) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_2130,c_1738])).

tff(c_2183,plain,(
    ! [A_340,B_341] : k5_xboole_0(A_340,k3_xboole_0(A_340,B_341)) = k4_xboole_0(A_340,B_341) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2192,plain,(
    ! [B_59] : k5_xboole_0('#skF_9','#skF_9') = k4_xboole_0('#skF_9',B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_2154,c_2183])).

tff(c_2196,plain,(
    ! [B_342] : k4_xboole_0('#skF_9',B_342) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2144,c_2192])).

tff(c_2201,plain,(
    ! [B_342] : r1_xboole_0('#skF_9',B_342) ),
    inference(superposition,[status(thm),theory(equality)],[c_2196,c_16])).

tff(c_2210,plain,(
    ! [A_344,B_345,C_346] :
      ( ~ r1_xboole_0(A_344,B_345)
      | ~ r2_hidden(C_346,k3_xboole_0(A_344,B_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2217,plain,(
    ! [B_59,C_346] :
      ( ~ r1_xboole_0('#skF_9',B_59)
      | ~ r2_hidden(C_346,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2154,c_2210])).

tff(c_2220,plain,(
    ! [C_346] : ~ r2_hidden(C_346,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2201,c_2217])).

tff(c_2389,plain,(
    ! [D_379,B_380] : ~ r2_hidden(D_379,k2_zfmisc_1('#skF_9',B_380)) ),
    inference(resolution,[status(thm)],[c_2374,c_2220])).

tff(c_2412,plain,(
    ! [B_380] : k2_zfmisc_1('#skF_9',B_380) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2181,c_2389])).

tff(c_2134,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_1734])).

tff(c_2180,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2134,c_2130,c_2134,c_52])).

tff(c_2416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_2180])).

tff(c_2418,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2420,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_6])).

tff(c_2855,plain,(
    ! [A_460,B_461,D_462] :
      ( r2_hidden('#skF_7'(A_460,B_461,k2_zfmisc_1(A_460,B_461),D_462),A_460)
      | ~ r2_hidden(D_462,k2_zfmisc_1(A_460,B_461)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2421,plain,(
    ! [B_59] : k3_xboole_0('#skF_12',B_59) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2418,c_75])).

tff(c_2716,plain,(
    ! [A_430,B_431,C_432] :
      ( ~ r1_xboole_0(A_430,B_431)
      | ~ r2_hidden(C_432,k3_xboole_0(A_430,B_431)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2723,plain,(
    ! [B_59,C_432] :
      ( ~ r1_xboole_0('#skF_12',B_59)
      | ~ r2_hidden(C_432,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2421,c_2716])).

tff(c_2725,plain,(
    ! [C_432] : ~ r2_hidden(C_432,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_2723])).

tff(c_2866,plain,(
    ! [D_463,B_464] : ~ r2_hidden(D_463,k2_zfmisc_1('#skF_12',B_464)) ),
    inference(resolution,[status(thm)],[c_2855,c_2725])).

tff(c_2881,plain,(
    ! [B_464] : k2_zfmisc_1('#skF_12',B_464) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2420,c_2866])).

tff(c_2610,plain,(
    ! [A_415,B_416,D_417] :
      ( r2_hidden('#skF_8'(A_415,B_416,k2_zfmisc_1(A_415,B_416),D_417),B_416)
      | ~ r2_hidden(D_417,k2_zfmisc_1(A_415,B_416)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2474,plain,(
    ! [A_385,B_386,C_387] :
      ( ~ r1_xboole_0(A_385,B_386)
      | ~ r2_hidden(C_387,k3_xboole_0(A_385,B_386)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2481,plain,(
    ! [B_59,C_387] :
      ( ~ r1_xboole_0('#skF_12',B_59)
      | ~ r2_hidden(C_387,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2421,c_2474])).

tff(c_2483,plain,(
    ! [C_387] : ~ r2_hidden(C_387,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_2481])).

tff(c_2621,plain,(
    ! [D_418,A_419] : ~ r2_hidden(D_418,k2_zfmisc_1(A_419,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_2610,c_2483])).

tff(c_2636,plain,(
    ! [A_419] : k2_zfmisc_1(A_419,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2420,c_2621])).

tff(c_2417,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2428,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2418,c_2417])).

tff(c_2429,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_2428])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2469,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2429,c_2418,c_48])).

tff(c_2640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_2469])).

tff(c_2641,plain,(
    ! [B_59] : ~ r1_xboole_0('#skF_12',B_59) ),
    inference(splitRight,[status(thm)],[c_2481])).

tff(c_2423,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_12') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_14])).

tff(c_2648,plain,(
    ! [A_423,B_424] : k5_xboole_0(A_423,k3_xboole_0(A_423,B_424)) = k4_xboole_0(A_423,B_424) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2657,plain,(
    ! [B_59] : k5_xboole_0('#skF_12','#skF_12') = k4_xboole_0('#skF_12',B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_2421,c_2648])).

tff(c_2661,plain,(
    ! [B_425] : k4_xboole_0('#skF_12',B_425) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2423,c_2657])).

tff(c_2666,plain,(
    ! [B_425] : r1_xboole_0('#skF_12',B_425) ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_16])).

tff(c_2671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2641,c_2666])).

tff(c_2672,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_2428])).

tff(c_2713,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_2672,c_2418,c_48])).

tff(c_2885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2881,c_2713])).

tff(c_2886,plain,(
    ! [B_59] : ~ r1_xboole_0('#skF_12',B_59) ),
    inference(splitRight,[status(thm)],[c_2723])).

tff(c_2919,plain,(
    ! [A_473,B_474] : k5_xboole_0(A_473,k3_xboole_0(A_473,B_474)) = k4_xboole_0(A_473,B_474) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2931,plain,(
    ! [B_59] : k5_xboole_0('#skF_12','#skF_12') = k4_xboole_0('#skF_12',B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_2421,c_2919])).

tff(c_2936,plain,(
    ! [B_475] : k4_xboole_0('#skF_12',B_475) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2423,c_2931])).

tff(c_2946,plain,(
    ! [B_475] : r1_xboole_0('#skF_12',B_475) ),
    inference(superposition,[status(thm),theory(equality)],[c_2936,c_16])).

tff(c_2953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2886,c_2946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.65  
% 3.63/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.65  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 3.63/1.65  
% 3.63/1.65  %Foreground sorts:
% 3.63/1.65  
% 3.63/1.65  
% 3.63/1.65  %Background operators:
% 3.63/1.65  
% 3.63/1.65  
% 3.63/1.65  %Foreground operators:
% 3.63/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.65  tff('#skF_11', type, '#skF_11': $i).
% 3.63/1.65  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.63/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.63/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.63/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.65  tff('#skF_10', type, '#skF_10': $i).
% 3.63/1.65  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.63/1.65  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.63/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.63/1.65  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.63/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.63/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.63/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.63/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.63/1.65  tff('#skF_12', type, '#skF_12': $i).
% 3.63/1.65  
% 3.63/1.68  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.63/1.68  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.63/1.68  tff(f_55, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.63/1.68  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.63/1.68  tff(f_84, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.63/1.68  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.63/1.68  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.63/1.68  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.63/1.68  tff(f_77, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.63/1.68  tff(f_71, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.63/1.68  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.63/1.68  tff(c_70, plain, (![A_58, B_59]: (r1_tarski(k3_xboole_0(A_58, B_59), A_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.63/1.68  tff(c_12, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.63/1.68  tff(c_75, plain, (![B_59]: (k3_xboole_0(k1_xboole_0, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_12])).
% 3.63/1.68  tff(c_795, plain, (![A_181, B_182, C_183]: (~r1_xboole_0(A_181, B_182) | ~r2_hidden(C_183, k3_xboole_0(A_181, B_182)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.68  tff(c_802, plain, (![B_59, C_183]: (~r1_xboole_0(k1_xboole_0, B_59) | ~r2_hidden(C_183, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_75, c_795])).
% 3.63/1.68  tff(c_805, plain, (![C_183]: (~r2_hidden(C_183, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_802])).
% 3.63/1.68  tff(c_50, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.63/1.68  tff(c_92, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_50])).
% 3.63/1.68  tff(c_54, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.63/1.68  tff(c_93, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_54])).
% 3.63/1.68  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.63/1.68  tff(c_100, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.68  tff(c_109, plain, (![B_59]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_59))), inference(superposition, [status(thm), theory('equality')], [c_75, c_100])).
% 3.63/1.68  tff(c_113, plain, (![B_64]: (k4_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_109])).
% 3.63/1.68  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.63/1.68  tff(c_118, plain, (![B_64]: (r1_xboole_0(k1_xboole_0, B_64))), inference(superposition, [status(thm), theory('equality')], [c_113, c_16])).
% 3.63/1.68  tff(c_123, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.68  tff(c_130, plain, (![B_59, C_67]: (~r1_xboole_0(k1_xboole_0, B_59) | ~r2_hidden(C_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_75, c_123])).
% 3.63/1.68  tff(c_134, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_130])).
% 3.63/1.68  tff(c_58, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.63/1.68  tff(c_95, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 3.63/1.68  tff(c_234, plain, (![A_88, B_89, C_90, D_91]: (r2_hidden(k4_tarski(A_88, B_89), k2_zfmisc_1(C_90, D_91)) | ~r2_hidden(B_89, D_91) | ~r2_hidden(A_88, C_90))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.63/1.68  tff(c_243, plain, (![A_88, B_89]: (r2_hidden(k4_tarski(A_88, B_89), k1_xboole_0) | ~r2_hidden(B_89, '#skF_12') | ~r2_hidden(A_88, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_234])).
% 3.63/1.68  tff(c_246, plain, (![B_89, A_88]: (~r2_hidden(B_89, '#skF_12') | ~r2_hidden(A_88, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_134, c_243])).
% 3.63/1.68  tff(c_248, plain, (![A_92]: (~r2_hidden(A_92, '#skF_11'))), inference(splitLeft, [status(thm)], [c_246])).
% 3.63/1.68  tff(c_252, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_6, c_248])).
% 3.63/1.68  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_252])).
% 3.63/1.68  tff(c_258, plain, (![B_93]: (~r2_hidden(B_93, '#skF_12'))), inference(splitRight, [status(thm)], [c_246])).
% 3.63/1.68  tff(c_262, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_6, c_258])).
% 3.63/1.68  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_262])).
% 3.63/1.68  tff(c_267, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_58])).
% 3.63/1.68  tff(c_269, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_267])).
% 3.63/1.68  tff(c_274, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_6])).
% 3.63/1.68  tff(c_480, plain, (![A_133, B_134, D_135]: (r2_hidden('#skF_8'(A_133, B_134, k2_zfmisc_1(A_133, B_134), D_135), B_134) | ~r2_hidden(D_135, k2_zfmisc_1(A_133, B_134)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.68  tff(c_277, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_10')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_269, c_14])).
% 3.63/1.68  tff(c_275, plain, (![B_59]: (k3_xboole_0('#skF_10', B_59)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_269, c_75])).
% 3.63/1.68  tff(c_316, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.68  tff(c_325, plain, (![B_59]: (k5_xboole_0('#skF_10', '#skF_10')=k4_xboole_0('#skF_10', B_59))), inference(superposition, [status(thm), theory('equality')], [c_275, c_316])).
% 3.63/1.68  tff(c_338, plain, (![B_103]: (k4_xboole_0('#skF_10', B_103)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_325])).
% 3.63/1.68  tff(c_343, plain, (![B_103]: (r1_xboole_0('#skF_10', B_103))), inference(superposition, [status(thm), theory('equality')], [c_338, c_16])).
% 3.63/1.68  tff(c_329, plain, (![A_100, B_101, C_102]: (~r1_xboole_0(A_100, B_101) | ~r2_hidden(C_102, k3_xboole_0(A_100, B_101)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.68  tff(c_336, plain, (![B_59, C_102]: (~r1_xboole_0('#skF_10', B_59) | ~r2_hidden(C_102, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_275, c_329])).
% 3.63/1.68  tff(c_350, plain, (![C_102]: (~r2_hidden(C_102, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_336])).
% 3.63/1.68  tff(c_524, plain, (![D_137, A_138]: (~r2_hidden(D_137, k2_zfmisc_1(A_138, '#skF_10')))), inference(resolution, [status(thm)], [c_480, c_350])).
% 3.63/1.68  tff(c_547, plain, (![A_138]: (k2_zfmisc_1(A_138, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_274, c_524])).
% 3.63/1.68  tff(c_56, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.63/1.68  tff(c_94, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 3.63/1.68  tff(c_270, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_269, c_94])).
% 3.63/1.68  tff(c_551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_547, c_270])).
% 3.63/1.68  tff(c_552, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_267])).
% 3.63/1.68  tff(c_559, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_552, c_6])).
% 3.63/1.68  tff(c_738, plain, (![A_173, B_174, D_175]: (r2_hidden('#skF_7'(A_173, B_174, k2_zfmisc_1(A_173, B_174), D_175), A_173) | ~r2_hidden(D_175, k2_zfmisc_1(A_173, B_174)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.68  tff(c_562, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_9')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_552, c_14])).
% 3.63/1.68  tff(c_560, plain, (![B_59]: (k3_xboole_0('#skF_9', B_59)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_552, c_552, c_75])).
% 3.63/1.68  tff(c_601, plain, (![A_143, B_144]: (k5_xboole_0(A_143, k3_xboole_0(A_143, B_144))=k4_xboole_0(A_143, B_144))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.68  tff(c_610, plain, (![B_59]: (k5_xboole_0('#skF_9', '#skF_9')=k4_xboole_0('#skF_9', B_59))), inference(superposition, [status(thm), theory('equality')], [c_560, c_601])).
% 3.63/1.68  tff(c_614, plain, (![B_145]: (k4_xboole_0('#skF_9', B_145)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_562, c_610])).
% 3.63/1.68  tff(c_619, plain, (![B_145]: (r1_xboole_0('#skF_9', B_145))), inference(superposition, [status(thm), theory('equality')], [c_614, c_16])).
% 3.63/1.68  tff(c_625, plain, (![A_147, B_148, C_149]: (~r1_xboole_0(A_147, B_148) | ~r2_hidden(C_149, k3_xboole_0(A_147, B_148)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.68  tff(c_632, plain, (![B_59, C_149]: (~r1_xboole_0('#skF_9', B_59) | ~r2_hidden(C_149, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_560, c_625])).
% 3.63/1.68  tff(c_635, plain, (![C_149]: (~r2_hidden(C_149, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_619, c_632])).
% 3.63/1.68  tff(c_760, plain, (![D_179, B_180]: (~r2_hidden(D_179, k2_zfmisc_1('#skF_9', B_180)))), inference(resolution, [status(thm)], [c_738, c_635])).
% 3.63/1.68  tff(c_780, plain, (![B_180]: (k2_zfmisc_1('#skF_9', B_180)='#skF_9')), inference(resolution, [status(thm)], [c_559, c_760])).
% 3.63/1.68  tff(c_555, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_552, c_94])).
% 3.63/1.68  tff(c_784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_780, c_555])).
% 3.63/1.68  tff(c_786, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 3.63/1.68  tff(c_935, plain, (![A_207, B_208, C_209, D_210]: (r2_hidden(k4_tarski(A_207, B_208), k2_zfmisc_1(C_209, D_210)) | ~r2_hidden(B_208, D_210) | ~r2_hidden(A_207, C_209))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.63/1.68  tff(c_944, plain, (![A_207, B_208]: (r2_hidden(k4_tarski(A_207, B_208), k1_xboole_0) | ~r2_hidden(B_208, '#skF_10') | ~r2_hidden(A_207, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_786, c_935])).
% 3.63/1.68  tff(c_950, plain, (![B_208, A_207]: (~r2_hidden(B_208, '#skF_10') | ~r2_hidden(A_207, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_805, c_944])).
% 3.63/1.68  tff(c_953, plain, (![A_211]: (~r2_hidden(A_211, '#skF_9'))), inference(splitLeft, [status(thm)], [c_950])).
% 3.63/1.68  tff(c_958, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6, c_953])).
% 3.63/1.68  tff(c_968, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_958, c_92])).
% 3.63/1.68  tff(c_1345, plain, (![A_245]: (r2_hidden('#skF_2'(A_245), A_245) | A_245='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_958, c_6])).
% 3.63/1.68  tff(c_967, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_958, c_93])).
% 3.63/1.68  tff(c_1195, plain, (![A_234]: (r2_hidden('#skF_2'(A_234), A_234) | A_234='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_958, c_6])).
% 3.63/1.68  tff(c_785, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 3.63/1.68  tff(c_947, plain, (![A_207, B_208]: (r2_hidden(k4_tarski(A_207, B_208), k1_xboole_0) | ~r2_hidden(B_208, '#skF_12') | ~r2_hidden(A_207, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_785, c_935])).
% 3.63/1.68  tff(c_951, plain, (![B_208, A_207]: (~r2_hidden(B_208, '#skF_12') | ~r2_hidden(A_207, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_805, c_947])).
% 3.63/1.68  tff(c_1149, plain, (![A_207]: (~r2_hidden(A_207, '#skF_11'))), inference(splitLeft, [status(thm)], [c_951])).
% 3.63/1.68  tff(c_1207, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_1195, c_1149])).
% 3.63/1.68  tff(c_1229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_967, c_1207])).
% 3.63/1.68  tff(c_1230, plain, (![B_208]: (~r2_hidden(B_208, '#skF_12'))), inference(splitRight, [status(thm)], [c_951])).
% 3.63/1.68  tff(c_1357, plain, ('#skF_9'='#skF_12'), inference(resolution, [status(thm)], [c_1345, c_1230])).
% 3.63/1.68  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_968, c_1357])).
% 3.63/1.68  tff(c_1392, plain, (![B_247]: (~r2_hidden(B_247, '#skF_10'))), inference(splitRight, [status(thm)], [c_950])).
% 3.63/1.68  tff(c_1397, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6, c_1392])).
% 3.63/1.68  tff(c_1407, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_92])).
% 3.63/1.68  tff(c_1635, plain, (![A_270]: (r2_hidden('#skF_2'(A_270), A_270) | A_270='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_6])).
% 3.63/1.68  tff(c_1382, plain, (![A_246]: (~r2_hidden(A_246, '#skF_11'))), inference(splitLeft, [status(thm)], [c_951])).
% 3.63/1.68  tff(c_1386, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_6, c_1382])).
% 3.63/1.68  tff(c_1390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_1386])).
% 3.63/1.68  tff(c_1391, plain, (![B_208]: (~r2_hidden(B_208, '#skF_12'))), inference(splitRight, [status(thm)], [c_951])).
% 3.63/1.68  tff(c_1655, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_1635, c_1391])).
% 3.63/1.68  tff(c_1671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1407, c_1655])).
% 3.63/1.68  tff(c_1672, plain, (![B_59]: (~r1_xboole_0(k1_xboole_0, B_59))), inference(splitRight, [status(thm)], [c_802])).
% 3.63/1.68  tff(c_1694, plain, (![A_276, B_277]: (k5_xboole_0(A_276, k3_xboole_0(A_276, B_277))=k4_xboole_0(A_276, B_277))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.68  tff(c_1706, plain, (![B_59]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_59))), inference(superposition, [status(thm), theory('equality')], [c_75, c_1694])).
% 3.63/1.68  tff(c_1718, plain, (![B_279]: (k4_xboole_0(k1_xboole_0, B_279)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1706])).
% 3.63/1.68  tff(c_1726, plain, (![B_279]: (r1_xboole_0(k1_xboole_0, B_279))), inference(superposition, [status(thm), theory('equality')], [c_1718, c_16])).
% 3.63/1.68  tff(c_1732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1672, c_1726])).
% 3.63/1.68  tff(c_1734, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_54])).
% 3.63/1.68  tff(c_1733, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 3.63/1.68  tff(c_1747, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_1734, c_1733])).
% 3.63/1.68  tff(c_1748, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_1747])).
% 3.63/1.68  tff(c_1737, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_6])).
% 3.63/1.68  tff(c_1797, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1748, c_1737])).
% 3.63/1.68  tff(c_2050, plain, (![A_327, B_328, D_329]: (r2_hidden('#skF_8'(A_327, B_328, k2_zfmisc_1(A_327, B_328), D_329), B_328) | ~r2_hidden(D_329, k2_zfmisc_1(A_327, B_328)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.68  tff(c_1738, plain, (![B_59]: (k3_xboole_0('#skF_11', B_59)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_1734, c_75])).
% 3.63/1.68  tff(c_1772, plain, (![B_59]: (k3_xboole_0('#skF_10', B_59)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1748, c_1748, c_1738])).
% 3.63/1.68  tff(c_1801, plain, (![A_284, B_285, C_286]: (~r1_xboole_0(A_284, B_285) | ~r2_hidden(C_286, k3_xboole_0(A_284, B_285)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.68  tff(c_1808, plain, (![B_59, C_286]: (~r1_xboole_0('#skF_10', B_59) | ~r2_hidden(C_286, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1772, c_1801])).
% 3.63/1.68  tff(c_1810, plain, (![C_286]: (~r2_hidden(C_286, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1808])).
% 3.63/1.68  tff(c_2073, plain, (![D_330, A_331]: (~r2_hidden(D_330, k2_zfmisc_1(A_331, '#skF_10')))), inference(resolution, [status(thm)], [c_2050, c_1810])).
% 3.63/1.68  tff(c_2099, plain, (![A_331]: (k2_zfmisc_1(A_331, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1797, c_2073])).
% 3.63/1.68  tff(c_1751, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1748, c_1734])).
% 3.63/1.68  tff(c_52, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.63/1.68  tff(c_1771, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1751, c_1748, c_1751, c_52])).
% 3.63/1.68  tff(c_2103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2099, c_1771])).
% 3.63/1.68  tff(c_2104, plain, (![B_59]: (~r1_xboole_0('#skF_10', B_59))), inference(splitRight, [status(thm)], [c_1808])).
% 3.63/1.68  tff(c_1740, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_11')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_1734, c_14])).
% 3.63/1.68  tff(c_1760, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_10')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_1748, c_1740])).
% 3.63/1.68  tff(c_2106, plain, (![A_333, B_334]: (k5_xboole_0(A_333, k3_xboole_0(A_333, B_334))=k4_xboole_0(A_333, B_334))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.68  tff(c_2115, plain, (![B_59]: (k5_xboole_0('#skF_10', '#skF_10')=k4_xboole_0('#skF_10', B_59))), inference(superposition, [status(thm), theory('equality')], [c_1772, c_2106])).
% 3.63/1.68  tff(c_2119, plain, (![B_335]: (k4_xboole_0('#skF_10', B_335)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1760, c_2115])).
% 3.63/1.68  tff(c_2124, plain, (![B_335]: (r1_xboole_0('#skF_10', B_335))), inference(superposition, [status(thm), theory('equality')], [c_2119, c_16])).
% 3.63/1.68  tff(c_2129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2104, c_2124])).
% 3.63/1.68  tff(c_2130, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_1747])).
% 3.63/1.68  tff(c_2181, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_1737])).
% 3.63/1.68  tff(c_2374, plain, (![A_376, B_377, D_378]: (r2_hidden('#skF_7'(A_376, B_377, k2_zfmisc_1(A_376, B_377), D_378), A_376) | ~r2_hidden(D_378, k2_zfmisc_1(A_376, B_377)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.68  tff(c_2144, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_9')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_1740])).
% 3.63/1.68  tff(c_2154, plain, (![B_59]: (k3_xboole_0('#skF_9', B_59)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_2130, c_1738])).
% 3.63/1.68  tff(c_2183, plain, (![A_340, B_341]: (k5_xboole_0(A_340, k3_xboole_0(A_340, B_341))=k4_xboole_0(A_340, B_341))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.68  tff(c_2192, plain, (![B_59]: (k5_xboole_0('#skF_9', '#skF_9')=k4_xboole_0('#skF_9', B_59))), inference(superposition, [status(thm), theory('equality')], [c_2154, c_2183])).
% 3.63/1.68  tff(c_2196, plain, (![B_342]: (k4_xboole_0('#skF_9', B_342)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2144, c_2192])).
% 3.63/1.68  tff(c_2201, plain, (![B_342]: (r1_xboole_0('#skF_9', B_342))), inference(superposition, [status(thm), theory('equality')], [c_2196, c_16])).
% 3.63/1.68  tff(c_2210, plain, (![A_344, B_345, C_346]: (~r1_xboole_0(A_344, B_345) | ~r2_hidden(C_346, k3_xboole_0(A_344, B_345)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.68  tff(c_2217, plain, (![B_59, C_346]: (~r1_xboole_0('#skF_9', B_59) | ~r2_hidden(C_346, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2154, c_2210])).
% 3.63/1.68  tff(c_2220, plain, (![C_346]: (~r2_hidden(C_346, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2201, c_2217])).
% 3.63/1.68  tff(c_2389, plain, (![D_379, B_380]: (~r2_hidden(D_379, k2_zfmisc_1('#skF_9', B_380)))), inference(resolution, [status(thm)], [c_2374, c_2220])).
% 3.63/1.68  tff(c_2412, plain, (![B_380]: (k2_zfmisc_1('#skF_9', B_380)='#skF_9')), inference(resolution, [status(thm)], [c_2181, c_2389])).
% 3.63/1.68  tff(c_2134, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_1734])).
% 3.63/1.68  tff(c_2180, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2134, c_2130, c_2134, c_52])).
% 3.63/1.68  tff(c_2416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2412, c_2180])).
% 3.63/1.68  tff(c_2418, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_50])).
% 3.63/1.68  tff(c_2420, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_6])).
% 3.63/1.68  tff(c_2855, plain, (![A_460, B_461, D_462]: (r2_hidden('#skF_7'(A_460, B_461, k2_zfmisc_1(A_460, B_461), D_462), A_460) | ~r2_hidden(D_462, k2_zfmisc_1(A_460, B_461)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.68  tff(c_2421, plain, (![B_59]: (k3_xboole_0('#skF_12', B_59)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2418, c_75])).
% 3.63/1.68  tff(c_2716, plain, (![A_430, B_431, C_432]: (~r1_xboole_0(A_430, B_431) | ~r2_hidden(C_432, k3_xboole_0(A_430, B_431)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.68  tff(c_2723, plain, (![B_59, C_432]: (~r1_xboole_0('#skF_12', B_59) | ~r2_hidden(C_432, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2421, c_2716])).
% 3.63/1.68  tff(c_2725, plain, (![C_432]: (~r2_hidden(C_432, '#skF_12'))), inference(splitLeft, [status(thm)], [c_2723])).
% 3.63/1.68  tff(c_2866, plain, (![D_463, B_464]: (~r2_hidden(D_463, k2_zfmisc_1('#skF_12', B_464)))), inference(resolution, [status(thm)], [c_2855, c_2725])).
% 3.63/1.68  tff(c_2881, plain, (![B_464]: (k2_zfmisc_1('#skF_12', B_464)='#skF_12')), inference(resolution, [status(thm)], [c_2420, c_2866])).
% 3.63/1.68  tff(c_2610, plain, (![A_415, B_416, D_417]: (r2_hidden('#skF_8'(A_415, B_416, k2_zfmisc_1(A_415, B_416), D_417), B_416) | ~r2_hidden(D_417, k2_zfmisc_1(A_415, B_416)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.63/1.68  tff(c_2474, plain, (![A_385, B_386, C_387]: (~r1_xboole_0(A_385, B_386) | ~r2_hidden(C_387, k3_xboole_0(A_385, B_386)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.68  tff(c_2481, plain, (![B_59, C_387]: (~r1_xboole_0('#skF_12', B_59) | ~r2_hidden(C_387, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2421, c_2474])).
% 3.63/1.68  tff(c_2483, plain, (![C_387]: (~r2_hidden(C_387, '#skF_12'))), inference(splitLeft, [status(thm)], [c_2481])).
% 3.63/1.68  tff(c_2621, plain, (![D_418, A_419]: (~r2_hidden(D_418, k2_zfmisc_1(A_419, '#skF_12')))), inference(resolution, [status(thm)], [c_2610, c_2483])).
% 3.63/1.68  tff(c_2636, plain, (![A_419]: (k2_zfmisc_1(A_419, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_2420, c_2621])).
% 3.63/1.68  tff(c_2417, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 3.63/1.68  tff(c_2428, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2418, c_2417])).
% 3.63/1.68  tff(c_2429, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_2428])).
% 3.63/1.68  tff(c_48, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.63/1.68  tff(c_2469, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2429, c_2418, c_48])).
% 3.63/1.68  tff(c_2640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2636, c_2469])).
% 3.63/1.68  tff(c_2641, plain, (![B_59]: (~r1_xboole_0('#skF_12', B_59))), inference(splitRight, [status(thm)], [c_2481])).
% 3.63/1.68  tff(c_2423, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_12')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_14])).
% 3.63/1.68  tff(c_2648, plain, (![A_423, B_424]: (k5_xboole_0(A_423, k3_xboole_0(A_423, B_424))=k4_xboole_0(A_423, B_424))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.68  tff(c_2657, plain, (![B_59]: (k5_xboole_0('#skF_12', '#skF_12')=k4_xboole_0('#skF_12', B_59))), inference(superposition, [status(thm), theory('equality')], [c_2421, c_2648])).
% 3.63/1.68  tff(c_2661, plain, (![B_425]: (k4_xboole_0('#skF_12', B_425)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2423, c_2657])).
% 3.63/1.68  tff(c_2666, plain, (![B_425]: (r1_xboole_0('#skF_12', B_425))), inference(superposition, [status(thm), theory('equality')], [c_2661, c_16])).
% 3.63/1.68  tff(c_2671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2641, c_2666])).
% 3.63/1.68  tff(c_2672, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_2428])).
% 3.63/1.68  tff(c_2713, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_2672, c_2418, c_48])).
% 3.63/1.68  tff(c_2885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2881, c_2713])).
% 3.63/1.68  tff(c_2886, plain, (![B_59]: (~r1_xboole_0('#skF_12', B_59))), inference(splitRight, [status(thm)], [c_2723])).
% 3.63/1.68  tff(c_2919, plain, (![A_473, B_474]: (k5_xboole_0(A_473, k3_xboole_0(A_473, B_474))=k4_xboole_0(A_473, B_474))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.63/1.68  tff(c_2931, plain, (![B_59]: (k5_xboole_0('#skF_12', '#skF_12')=k4_xboole_0('#skF_12', B_59))), inference(superposition, [status(thm), theory('equality')], [c_2421, c_2919])).
% 3.63/1.68  tff(c_2936, plain, (![B_475]: (k4_xboole_0('#skF_12', B_475)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2423, c_2931])).
% 3.63/1.68  tff(c_2946, plain, (![B_475]: (r1_xboole_0('#skF_12', B_475))), inference(superposition, [status(thm), theory('equality')], [c_2936, c_16])).
% 3.63/1.68  tff(c_2953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2886, c_2946])).
% 3.63/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.68  
% 3.63/1.68  Inference rules
% 3.63/1.68  ----------------------
% 3.63/1.68  #Ref     : 0
% 3.63/1.68  #Sup     : 621
% 3.63/1.68  #Fact    : 0
% 3.63/1.68  #Define  : 0
% 3.63/1.68  #Split   : 17
% 3.63/1.68  #Chain   : 0
% 3.63/1.68  #Close   : 0
% 3.63/1.68  
% 3.63/1.68  Ordering : KBO
% 3.63/1.68  
% 3.63/1.68  Simplification rules
% 3.63/1.68  ----------------------
% 3.63/1.68  #Subsume      : 119
% 3.63/1.68  #Demod        : 400
% 3.63/1.68  #Tautology    : 344
% 3.63/1.68  #SimpNegUnit  : 56
% 3.63/1.68  #BackRed      : 79
% 3.63/1.68  
% 3.63/1.68  #Partial instantiations: 0
% 3.63/1.68  #Strategies tried      : 1
% 3.63/1.68  
% 3.63/1.68  Timing (in seconds)
% 3.63/1.68  ----------------------
% 3.63/1.68  Preprocessing        : 0.32
% 3.63/1.68  Parsing              : 0.16
% 3.63/1.68  CNF conversion       : 0.03
% 3.63/1.68  Main loop            : 0.55
% 3.63/1.68  Inferencing          : 0.23
% 3.63/1.68  Reduction            : 0.17
% 3.63/1.68  Demodulation         : 0.11
% 3.63/1.68  BG Simplification    : 0.02
% 3.63/1.68  Subsumption          : 0.08
% 3.63/1.68  Abstraction          : 0.03
% 3.63/1.68  MUC search           : 0.00
% 3.63/1.68  Cooper               : 0.00
% 3.63/1.68  Total                : 0.94
% 3.63/1.68  Index Insertion      : 0.00
% 3.63/1.68  Index Deletion       : 0.00
% 3.63/1.68  Index Matching       : 0.00
% 3.63/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
