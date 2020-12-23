%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:09 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 249 expanded)
%              Number of leaves         :   41 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 338 expanded)
%              Number of equality atoms :   84 ( 188 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_63,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_77,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_88,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_324,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_336,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_324])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_335,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_324])).

tff(c_38,plain,(
    ! [A_32] : k2_subset_1(A_32) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_35] : m1_subset_1(k2_subset_1(A_35),k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    ! [A_35] : m1_subset_1(A_35,k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_890,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k3_subset_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_896,plain,(
    ! [A_35] : k4_xboole_0(A_35,A_35) = k3_subset_1(A_35,A_35) ),
    inference(resolution,[status(thm)],[c_64,c_890])).

tff(c_900,plain,(
    ! [A_35] : k3_subset_1(A_35,A_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_896])).

tff(c_225,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | k4_xboole_0(A_61,B_62) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_65,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_62])).

tff(c_131,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_56,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56])).

tff(c_224,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_131,c_66])).

tff(c_229,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_1'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_224])).

tff(c_901,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_229])).

tff(c_905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_901])).

tff(c_907,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_36,plain,(
    ! [A_31] : k1_subset_1(A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    ! [A_38] : k3_subset_1(A_38,k1_subset_1(A_38)) = k2_subset_1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_63,plain,(
    ! [A_38] : k3_subset_1(A_38,k1_subset_1(A_38)) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_67,plain,(
    ! [A_38] : k3_subset_1(A_38,k1_xboole_0) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_63])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1791,plain,(
    ! [A_158,B_159] :
      ( k4_xboole_0(A_158,B_159) = k3_subset_1(A_158,B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1801,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1791])).

tff(c_1190,plain,(
    ! [A_122,B_123] :
      ( r1_tarski(A_122,B_123)
      | k4_xboole_0(A_122,B_123) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1194,plain,(
    ! [A_122,B_123] :
      ( k3_xboole_0(A_122,B_123) = A_122
      | k4_xboole_0(A_122,B_123) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1190,c_18])).

tff(c_1810,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k3_subset_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1801,c_1194])).

tff(c_1821,plain,(
    k3_subset_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1810])).

tff(c_52,plain,(
    ! [A_43] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1759,plain,(
    ! [A_155,B_156] :
      ( k3_subset_1(A_155,k3_subset_1(A_155,B_156)) = B_156
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1763,plain,(
    ! [A_43] : k3_subset_1(A_43,k3_subset_1(A_43,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1759])).

tff(c_1768,plain,(
    ! [A_43] : k3_subset_1(A_43,A_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1763])).

tff(c_2186,plain,(
    ! [B_174,C_175,A_176] :
      ( r1_tarski(B_174,C_175)
      | ~ r1_tarski(k3_subset_1(A_176,C_175),k3_subset_1(A_176,B_174))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(A_176))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2195,plain,(
    ! [B_174,A_43] :
      ( r1_tarski(B_174,A_43)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_43,B_174))
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_2186])).

tff(c_2223,plain,(
    ! [B_177,A_178] :
      ( r1_tarski(B_177,A_178)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(A_178)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20,c_2195])).

tff(c_2233,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_2223])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2255,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2233,c_12])).

tff(c_906,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_962,plain,(
    ! [A_109,B_110] :
      ( k3_xboole_0(A_109,B_110) = A_109
      | ~ r1_tarski(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_972,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_906,c_962])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1095,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_2])).

tff(c_975,plain,(
    ! [B_111] : k3_xboole_0(B_111,B_111) = B_111 ),
    inference(resolution,[status(thm)],[c_8,c_962])).

tff(c_16,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_981,plain,(
    ! [B_111] : k2_xboole_0(B_111,B_111) = B_111 ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_16])).

tff(c_1195,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(A_124,B_125) = k1_xboole_0
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1210,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1195])).

tff(c_1377,plain,(
    ! [A_133,B_134] : k5_xboole_0(A_133,k4_xboole_0(B_134,A_133)) = k2_xboole_0(A_133,B_134) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1392,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_1377])).

tff(c_1397,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_1392])).

tff(c_24,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2279,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2255,c_24])).

tff(c_2289,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_2279])).

tff(c_26,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1175,plain,(
    ! [A_120,B_121] : k3_tarski(k2_tarski(A_120,B_121)) = k2_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1238,plain,(
    ! [B_128,A_129] : k3_tarski(k2_tarski(B_128,A_129)) = k2_xboole_0(A_129,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1175])).

tff(c_34,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1244,plain,(
    ! [B_128,A_129] : k2_xboole_0(B_128,A_129) = k2_xboole_0(A_129,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_34])).

tff(c_1816,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1801,c_24])).

tff(c_1819,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1816])).

tff(c_1427,plain,(
    ! [A_136,B_137] : k5_xboole_0(A_136,k3_xboole_0(A_136,B_137)) = k4_xboole_0(A_136,B_137) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1645,plain,(
    ! [B_146,A_147] : k5_xboole_0(B_146,k3_xboole_0(A_147,B_146)) = k4_xboole_0(B_146,A_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1427])).

tff(c_1673,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_1645])).

tff(c_2156,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1819,c_1673])).

tff(c_2416,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2289,c_2156])).

tff(c_22,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2518,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2416,c_22])).

tff(c_2529,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_1095,c_2518])).

tff(c_2531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1821,c_2529])).

tff(c_2533,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1810])).

tff(c_1766,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_1759])).

tff(c_2553,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_1766])).

tff(c_2561,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2553])).

tff(c_2563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_907,c_2561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.60  
% 3.40/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.61  %$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.40/1.61  
% 3.40/1.61  %Foreground sorts:
% 3.40/1.61  
% 3.40/1.61  
% 3.40/1.61  %Background operators:
% 3.40/1.61  
% 3.40/1.61  
% 3.40/1.61  %Foreground operators:
% 3.40/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.40/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.61  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.40/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.40/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.61  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.40/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.40/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.61  
% 3.40/1.62  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.40/1.62  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.40/1.62  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.40/1.62  tff(f_65, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.40/1.62  tff(f_71, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.40/1.62  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.40/1.62  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.40/1.62  tff(f_63, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.40/1.62  tff(f_77, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.40/1.62  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.40/1.62  tff(f_88, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.40/1.62  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.40/1.62  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.40/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.40/1.62  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.40/1.62  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.40/1.62  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.40/1.62  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.40/1.62  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.40/1.62  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.40/1.62  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.62  tff(c_324, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.62  tff(c_336, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_324])).
% 3.40/1.62  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.62  tff(c_335, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_324])).
% 3.40/1.62  tff(c_38, plain, (![A_32]: (k2_subset_1(A_32)=A_32)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.62  tff(c_42, plain, (![A_35]: (m1_subset_1(k2_subset_1(A_35), k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.40/1.62  tff(c_64, plain, (![A_35]: (m1_subset_1(A_35, k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 3.40/1.62  tff(c_890, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k3_subset_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.62  tff(c_896, plain, (![A_35]: (k4_xboole_0(A_35, A_35)=k3_subset_1(A_35, A_35))), inference(resolution, [status(thm)], [c_64, c_890])).
% 3.40/1.62  tff(c_900, plain, (![A_35]: (k3_subset_1(A_35, A_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_335, c_896])).
% 3.40/1.62  tff(c_225, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | k4_xboole_0(A_61, B_62)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.62  tff(c_62, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.40/1.62  tff(c_65, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_62])).
% 3.40/1.62  tff(c_131, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_65])).
% 3.40/1.62  tff(c_56, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.40/1.62  tff(c_66, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56])).
% 3.40/1.62  tff(c_224, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_131, c_66])).
% 3.40/1.62  tff(c_229, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_225, c_224])).
% 3.40/1.62  tff(c_901, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_900, c_229])).
% 3.40/1.62  tff(c_905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_336, c_901])).
% 3.40/1.62  tff(c_907, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_65])).
% 3.40/1.62  tff(c_36, plain, (![A_31]: (k1_subset_1(A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.40/1.62  tff(c_46, plain, (![A_38]: (k3_subset_1(A_38, k1_subset_1(A_38))=k2_subset_1(A_38))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.40/1.62  tff(c_63, plain, (![A_38]: (k3_subset_1(A_38, k1_subset_1(A_38))=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 3.40/1.62  tff(c_67, plain, (![A_38]: (k3_subset_1(A_38, k1_xboole_0)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_63])).
% 3.40/1.62  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.40/1.62  tff(c_1791, plain, (![A_158, B_159]: (k4_xboole_0(A_158, B_159)=k3_subset_1(A_158, B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.62  tff(c_1801, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_1791])).
% 3.40/1.62  tff(c_1190, plain, (![A_122, B_123]: (r1_tarski(A_122, B_123) | k4_xboole_0(A_122, B_123)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.62  tff(c_18, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.62  tff(c_1194, plain, (![A_122, B_123]: (k3_xboole_0(A_122, B_123)=A_122 | k4_xboole_0(A_122, B_123)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1190, c_18])).
% 3.40/1.62  tff(c_1810, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k3_subset_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1801, c_1194])).
% 3.40/1.62  tff(c_1821, plain, (k3_subset_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1810])).
% 3.40/1.62  tff(c_52, plain, (![A_43]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.40/1.62  tff(c_1759, plain, (![A_155, B_156]: (k3_subset_1(A_155, k3_subset_1(A_155, B_156))=B_156 | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.40/1.62  tff(c_1763, plain, (![A_43]: (k3_subset_1(A_43, k3_subset_1(A_43, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_1759])).
% 3.40/1.62  tff(c_1768, plain, (![A_43]: (k3_subset_1(A_43, A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1763])).
% 3.40/1.62  tff(c_2186, plain, (![B_174, C_175, A_176]: (r1_tarski(B_174, C_175) | ~r1_tarski(k3_subset_1(A_176, C_175), k3_subset_1(A_176, B_174)) | ~m1_subset_1(C_175, k1_zfmisc_1(A_176)) | ~m1_subset_1(B_174, k1_zfmisc_1(A_176)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.40/1.62  tff(c_2195, plain, (![B_174, A_43]: (r1_tarski(B_174, A_43) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_43, B_174)) | ~m1_subset_1(A_43, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_174, k1_zfmisc_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_1768, c_2186])).
% 3.40/1.62  tff(c_2223, plain, (![B_177, A_178]: (r1_tarski(B_177, A_178) | ~m1_subset_1(B_177, k1_zfmisc_1(A_178)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20, c_2195])).
% 3.40/1.62  tff(c_2233, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_2223])).
% 3.40/1.62  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.62  tff(c_2255, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_2233, c_12])).
% 3.40/1.62  tff(c_906, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_65])).
% 3.40/1.62  tff(c_962, plain, (![A_109, B_110]: (k3_xboole_0(A_109, B_110)=A_109 | ~r1_tarski(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.62  tff(c_972, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_906, c_962])).
% 3.40/1.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.62  tff(c_1095, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_972, c_2])).
% 3.40/1.62  tff(c_975, plain, (![B_111]: (k3_xboole_0(B_111, B_111)=B_111)), inference(resolution, [status(thm)], [c_8, c_962])).
% 3.40/1.62  tff(c_16, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.62  tff(c_981, plain, (![B_111]: (k2_xboole_0(B_111, B_111)=B_111)), inference(superposition, [status(thm), theory('equality')], [c_975, c_16])).
% 3.40/1.62  tff(c_1195, plain, (![A_124, B_125]: (k4_xboole_0(A_124, B_125)=k1_xboole_0 | ~r1_tarski(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.62  tff(c_1210, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1195])).
% 3.40/1.62  tff(c_1377, plain, (![A_133, B_134]: (k5_xboole_0(A_133, k4_xboole_0(B_134, A_133))=k2_xboole_0(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.40/1.62  tff(c_1392, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_1377])).
% 3.40/1.62  tff(c_1397, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_981, c_1392])).
% 3.40/1.62  tff(c_24, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.40/1.62  tff(c_2279, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2255, c_24])).
% 3.40/1.62  tff(c_2289, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_2279])).
% 3.40/1.62  tff(c_26, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.62  tff(c_1175, plain, (![A_120, B_121]: (k3_tarski(k2_tarski(A_120, B_121))=k2_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.62  tff(c_1238, plain, (![B_128, A_129]: (k3_tarski(k2_tarski(B_128, A_129))=k2_xboole_0(A_129, B_128))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1175])).
% 3.40/1.62  tff(c_34, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.62  tff(c_1244, plain, (![B_128, A_129]: (k2_xboole_0(B_128, A_129)=k2_xboole_0(A_129, B_128))), inference(superposition, [status(thm), theory('equality')], [c_1238, c_34])).
% 3.40/1.62  tff(c_1816, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1801, c_24])).
% 3.40/1.62  tff(c_1819, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1816])).
% 3.40/1.62  tff(c_1427, plain, (![A_136, B_137]: (k5_xboole_0(A_136, k3_xboole_0(A_136, B_137))=k4_xboole_0(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.62  tff(c_1645, plain, (![B_146, A_147]: (k5_xboole_0(B_146, k3_xboole_0(A_147, B_146))=k4_xboole_0(B_146, A_147))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1427])).
% 3.40/1.62  tff(c_1673, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_972, c_1645])).
% 3.40/1.62  tff(c_2156, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1819, c_1673])).
% 3.40/1.62  tff(c_2416, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2289, c_2156])).
% 3.40/1.62  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.62  tff(c_2518, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2416, c_22])).
% 3.40/1.62  tff(c_2529, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_1095, c_2518])).
% 3.40/1.62  tff(c_2531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1821, c_2529])).
% 3.40/1.62  tff(c_2533, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1810])).
% 3.40/1.62  tff(c_1766, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_54, c_1759])).
% 3.40/1.62  tff(c_2553, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_1766])).
% 3.40/1.62  tff(c_2561, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2553])).
% 3.40/1.62  tff(c_2563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_907, c_2561])).
% 3.40/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.62  
% 3.40/1.62  Inference rules
% 3.40/1.62  ----------------------
% 3.40/1.62  #Ref     : 0
% 3.40/1.62  #Sup     : 597
% 3.40/1.62  #Fact    : 0
% 3.40/1.62  #Define  : 0
% 3.40/1.62  #Split   : 6
% 3.40/1.62  #Chain   : 0
% 3.40/1.63  #Close   : 0
% 3.40/1.63  
% 3.40/1.63  Ordering : KBO
% 3.40/1.63  
% 3.40/1.63  Simplification rules
% 3.40/1.63  ----------------------
% 3.40/1.63  #Subsume      : 20
% 3.40/1.63  #Demod        : 399
% 3.40/1.63  #Tautology    : 440
% 3.40/1.63  #SimpNegUnit  : 8
% 3.40/1.63  #BackRed      : 18
% 3.40/1.63  
% 3.40/1.63  #Partial instantiations: 0
% 3.40/1.63  #Strategies tried      : 1
% 3.40/1.63  
% 3.40/1.63  Timing (in seconds)
% 3.40/1.63  ----------------------
% 3.81/1.63  Preprocessing        : 0.31
% 3.81/1.63  Parsing              : 0.16
% 3.81/1.63  CNF conversion       : 0.02
% 3.81/1.63  Main loop            : 0.55
% 3.81/1.63  Inferencing          : 0.18
% 3.81/1.63  Reduction            : 0.22
% 3.81/1.63  Demodulation         : 0.17
% 3.81/1.63  BG Simplification    : 0.03
% 3.81/1.63  Subsumption          : 0.09
% 3.81/1.63  Abstraction          : 0.03
% 3.81/1.63  MUC search           : 0.00
% 3.81/1.63  Cooper               : 0.00
% 3.81/1.63  Total                : 0.90
% 3.81/1.63  Index Insertion      : 0.00
% 3.81/1.63  Index Deletion       : 0.00
% 3.81/1.63  Index Matching       : 0.00
% 3.81/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
