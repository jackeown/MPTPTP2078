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
% DateTime   : Thu Dec  3 09:43:49 EST 2020

% Result     : Theorem 5.88s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 545 expanded)
%              Number of leaves         :   29 ( 197 expanded)
%              Depth                    :   18
%              Number of atoms          :  117 ( 824 expanded)
%              Number of equality atoms :   75 ( 491 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_48,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_310,plain,(
    ! [A_59,B_60] : k4_xboole_0(k2_xboole_0(A_59,B_60),B_60) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_347,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_310])).

tff(c_36,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_225,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = k3_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_246,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k3_xboole_0(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_225])).

tff(c_28,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_2'(A_10,B_11,C_12),A_10)
      | r2_hidden('#skF_3'(A_10,B_11,C_12),C_12)
      | k4_xboole_0(A_10,B_11) = C_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2065,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r2_hidden('#skF_2'(A_121,B_122,C_123),B_122)
      | r2_hidden('#skF_3'(A_121,B_122,C_123),C_123)
      | k4_xboole_0(A_121,B_122) = C_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2071,plain,(
    ! [A_10,C_12] :
      ( r2_hidden('#skF_3'(A_10,A_10,C_12),C_12)
      | k4_xboole_0(A_10,A_10) = C_12 ) ),
    inference(resolution,[status(thm)],[c_28,c_2065])).

tff(c_2078,plain,(
    ! [A_10,C_12] :
      ( r2_hidden('#skF_3'(A_10,A_10,C_12),C_12)
      | k3_xboole_0(A_10,k1_xboole_0) = C_12 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_2071])).

tff(c_3250,plain,(
    ! [A_155,C_156] :
      ( r2_hidden('#skF_3'(A_155,A_155,C_156),C_156)
      | k3_xboole_0(A_155,k1_xboole_0) = C_156 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_2071])).

tff(c_211,plain,(
    ! [D_44,B_45,A_46] :
      ( ~ r2_hidden(D_44,B_45)
      | ~ r2_hidden(D_44,k4_xboole_0(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_214,plain,(
    ! [D_44,A_23] :
      ( ~ r2_hidden(D_44,k1_xboole_0)
      | ~ r2_hidden(D_44,A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_211])).

tff(c_3630,plain,(
    ! [A_166,A_167] :
      ( ~ r2_hidden('#skF_3'(A_166,A_166,k1_xboole_0),A_167)
      | k3_xboole_0(A_166,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3250,c_214])).

tff(c_3672,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2078,c_3630])).

tff(c_3701,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_246])).

tff(c_830,plain,(
    ! [A_85,B_86,C_87] : k4_xboole_0(k4_xboole_0(A_85,B_86),C_87) = k4_xboole_0(A_85,k2_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4867,plain,(
    ! [C_197,A_198,B_199] : k2_xboole_0(C_197,k4_xboole_0(A_198,k2_xboole_0(B_199,C_197))) = k2_xboole_0(C_197,k4_xboole_0(A_198,B_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_38])).

tff(c_4930,plain,(
    ! [C_197,B_199] : k2_xboole_0(C_197,k4_xboole_0(k2_xboole_0(B_199,C_197),B_199)) = k2_xboole_0(C_197,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3701,c_4867])).

tff(c_4996,plain,(
    ! [C_197,B_199] : k2_xboole_0(C_197,k4_xboole_0(C_197,B_199)) = C_197 ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_36,c_4930])).

tff(c_50,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_198,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_206,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_198])).

tff(c_46,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3031,plain,(
    ! [A_150,B_151] : k4_xboole_0(A_150,k3_xboole_0(A_150,B_151)) = k3_xboole_0(A_150,k4_xboole_0(A_150,B_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_225])).

tff(c_3125,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_3031])).

tff(c_3153,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3125])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_899,plain,(
    ! [A_29,B_30,C_87] : k4_xboole_0(A_29,k2_xboole_0(k4_xboole_0(A_29,B_30),C_87)) = k4_xboole_0(k3_xboole_0(A_29,B_30),C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_830])).

tff(c_105,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_121,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_36])).

tff(c_341,plain,(
    ! [A_36] : k4_xboole_0(k1_xboole_0,A_36) = k4_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_310])).

tff(c_361,plain,(
    ! [A_36] : k4_xboole_0(k1_xboole_0,A_36) = k3_xboole_0(A_36,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_341])).

tff(c_574,plain,(
    ! [A_68,B_69] : k4_xboole_0(k2_xboole_0(A_68,B_69),A_68) = k4_xboole_0(B_69,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_310])).

tff(c_616,plain,(
    ! [B_22,A_21] : k4_xboole_0(k4_xboole_0(B_22,A_21),A_21) = k4_xboole_0(k2_xboole_0(A_21,B_22),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_574])).

tff(c_1048,plain,(
    ! [B_93,A_94] : k4_xboole_0(k4_xboole_0(B_93,A_94),A_94) = k4_xboole_0(B_93,A_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_616])).

tff(c_1101,plain,(
    ! [A_36] : k4_xboole_0(k3_xboole_0(A_36,k1_xboole_0),A_36) = k4_xboole_0(k1_xboole_0,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_1048])).

tff(c_1132,plain,(
    ! [A_36] : k4_xboole_0(k3_xboole_0(A_36,k1_xboole_0),A_36) = k3_xboole_0(A_36,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_1101])).

tff(c_3694,plain,(
    ! [A_36] : k4_xboole_0(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3672,c_1132])).

tff(c_4103,plain,(
    ! [A_176,B_177,C_178] : k4_xboole_0(A_176,k2_xboole_0(k4_xboole_0(A_176,B_177),C_178)) = k4_xboole_0(k3_xboole_0(A_176,B_177),C_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_830])).

tff(c_4212,plain,(
    ! [A_23,C_178] : k4_xboole_0(k3_xboole_0(A_23,k1_xboole_0),C_178) = k4_xboole_0(A_23,k2_xboole_0(A_23,C_178)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4103])).

tff(c_4299,plain,(
    ! [A_181,C_182] : k4_xboole_0(A_181,k2_xboole_0(A_181,C_182)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3694,c_3672,c_4212])).

tff(c_4555,plain,(
    ! [B_187,A_188] : k4_xboole_0(B_187,k2_xboole_0(A_188,B_187)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4299])).

tff(c_5819,plain,(
    ! [C_215,B_216] : k4_xboole_0(k3_xboole_0(C_215,B_216),C_215) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_4555])).

tff(c_6144,plain,(
    ! [A_220,B_221] : k4_xboole_0(k3_xboole_0(A_220,B_221),B_221) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5819])).

tff(c_6236,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3153,c_6144])).

tff(c_335,plain,(
    ! [A_21,B_22] : k4_xboole_0(k2_xboole_0(A_21,B_22),k4_xboole_0(B_22,A_21)) = k4_xboole_0(A_21,k4_xboole_0(B_22,A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_310])).

tff(c_6290,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_6'),k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6'))) = k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_4','#skF_6'),'#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6236,c_335])).

tff(c_6332,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4996,c_40,c_206,c_46,c_2,c_40,c_6290])).

tff(c_364,plain,(
    ! [A_61] : k4_xboole_0(k1_xboole_0,A_61) = k3_xboole_0(A_61,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_341])).

tff(c_402,plain,(
    ! [B_30] : k3_xboole_0(k4_xboole_0(k1_xboole_0,B_30),k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_364])).

tff(c_414,plain,(
    ! [B_30] : k3_xboole_0(k1_xboole_0,k3_xboole_0(B_30,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_361,c_402])).

tff(c_3692,plain,(
    ! [B_30] : k3_xboole_0(k1_xboole_0,B_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3672,c_414])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_53,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_190,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_194,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_53,c_190])).

tff(c_338,plain,(
    k4_xboole_0(k2_xboole_0('#skF_6','#skF_5'),k2_xboole_0('#skF_6','#skF_5')) = k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_310])).

tff(c_360,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k3_xboole_0(k1_xboole_0,k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_246,c_338])).

tff(c_3791,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3692,c_360])).

tff(c_4923,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_6')) = k2_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3791,c_4867])).

tff(c_4994,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4923])).

tff(c_6345,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6332,c_4994])).

tff(c_4335,plain,(
    ! [A_181,C_182] : k3_xboole_0(A_181,k2_xboole_0(A_181,C_182)) = k4_xboole_0(A_181,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4299,c_46])).

tff(c_4787,plain,(
    ! [A_195,C_196] : k3_xboole_0(A_195,k2_xboole_0(A_195,C_196)) = A_195 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4335])).

tff(c_4831,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4787])).

tff(c_6470,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6345,c_4831])).

tff(c_516,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,A_10)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6587,plain,(
    ! [A_222,B_223,B_224] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_222,B_223),B_224),A_222)
      | r1_tarski(k4_xboole_0(A_222,B_223),B_224) ) ),
    inference(resolution,[status(thm)],[c_516,c_16])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7120,plain,(
    ! [A_228,B_229] : r1_tarski(k4_xboole_0(A_228,B_229),A_228) ),
    inference(resolution,[status(thm)],[c_6587,c_8])).

tff(c_7216,plain,(
    ! [A_230,B_231] : r1_tarski(k3_xboole_0(A_230,B_231),A_230) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_7120])).

tff(c_7272,plain,(
    ! [B_232,A_233] : r1_tarski(k3_xboole_0(B_232,A_233),A_233) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7216])).

tff(c_7286,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6470,c_7272])).

tff(c_7320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_7286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.88/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.25  
% 5.88/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.88/2.25  
% 5.88/2.25  %Foreground sorts:
% 5.88/2.25  
% 5.88/2.25  
% 5.88/2.25  %Background operators:
% 5.88/2.25  
% 5.88/2.25  
% 5.88/2.25  %Foreground operators:
% 5.88/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.88/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.88/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.88/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.88/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.88/2.25  tff('#skF_5', type, '#skF_5': $i).
% 5.88/2.25  tff('#skF_6', type, '#skF_6': $i).
% 5.88/2.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.88/2.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.88/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.88/2.25  tff('#skF_4', type, '#skF_4': $i).
% 5.88/2.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.88/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.88/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.88/2.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.88/2.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.88/2.25  
% 5.88/2.27  tff(f_73, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 5.88/2.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.88/2.27  tff(f_62, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.88/2.27  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.88/2.27  tff(f_60, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.88/2.27  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.88/2.27  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.88/2.27  tff(f_64, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.88/2.27  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.88/2.27  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.88/2.27  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.88/2.27  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.88/2.27  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.88/2.27  tff(c_48, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.88/2.27  tff(c_310, plain, (![A_59, B_60]: (k4_xboole_0(k2_xboole_0(A_59, B_60), B_60)=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.88/2.27  tff(c_347, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_310])).
% 5.88/2.27  tff(c_36, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.88/2.27  tff(c_40, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.88/2.27  tff(c_225, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k4_xboole_0(A_54, B_55))=k3_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.88/2.27  tff(c_246, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k3_xboole_0(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_225])).
% 5.88/2.27  tff(c_28, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_2'(A_10, B_11, C_12), A_10) | r2_hidden('#skF_3'(A_10, B_11, C_12), C_12) | k4_xboole_0(A_10, B_11)=C_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.27  tff(c_2065, plain, (![A_121, B_122, C_123]: (~r2_hidden('#skF_2'(A_121, B_122, C_123), B_122) | r2_hidden('#skF_3'(A_121, B_122, C_123), C_123) | k4_xboole_0(A_121, B_122)=C_123)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.27  tff(c_2071, plain, (![A_10, C_12]: (r2_hidden('#skF_3'(A_10, A_10, C_12), C_12) | k4_xboole_0(A_10, A_10)=C_12)), inference(resolution, [status(thm)], [c_28, c_2065])).
% 5.88/2.27  tff(c_2078, plain, (![A_10, C_12]: (r2_hidden('#skF_3'(A_10, A_10, C_12), C_12) | k3_xboole_0(A_10, k1_xboole_0)=C_12)), inference(demodulation, [status(thm), theory('equality')], [c_246, c_2071])).
% 5.88/2.27  tff(c_3250, plain, (![A_155, C_156]: (r2_hidden('#skF_3'(A_155, A_155, C_156), C_156) | k3_xboole_0(A_155, k1_xboole_0)=C_156)), inference(demodulation, [status(thm), theory('equality')], [c_246, c_2071])).
% 5.88/2.27  tff(c_211, plain, (![D_44, B_45, A_46]: (~r2_hidden(D_44, B_45) | ~r2_hidden(D_44, k4_xboole_0(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.27  tff(c_214, plain, (![D_44, A_23]: (~r2_hidden(D_44, k1_xboole_0) | ~r2_hidden(D_44, A_23))), inference(superposition, [status(thm), theory('equality')], [c_40, c_211])).
% 5.88/2.27  tff(c_3630, plain, (![A_166, A_167]: (~r2_hidden('#skF_3'(A_166, A_166, k1_xboole_0), A_167) | k3_xboole_0(A_166, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3250, c_214])).
% 5.88/2.27  tff(c_3672, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2078, c_3630])).
% 5.88/2.27  tff(c_3701, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_246])).
% 5.88/2.27  tff(c_830, plain, (![A_85, B_86, C_87]: (k4_xboole_0(k4_xboole_0(A_85, B_86), C_87)=k4_xboole_0(A_85, k2_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.88/2.27  tff(c_38, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.88/2.27  tff(c_4867, plain, (![C_197, A_198, B_199]: (k2_xboole_0(C_197, k4_xboole_0(A_198, k2_xboole_0(B_199, C_197)))=k2_xboole_0(C_197, k4_xboole_0(A_198, B_199)))), inference(superposition, [status(thm), theory('equality')], [c_830, c_38])).
% 5.88/2.27  tff(c_4930, plain, (![C_197, B_199]: (k2_xboole_0(C_197, k4_xboole_0(k2_xboole_0(B_199, C_197), B_199))=k2_xboole_0(C_197, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3701, c_4867])).
% 5.88/2.27  tff(c_4996, plain, (![C_197, B_199]: (k2_xboole_0(C_197, k4_xboole_0(C_197, B_199))=C_197)), inference(demodulation, [status(thm), theory('equality')], [c_347, c_36, c_4930])).
% 5.88/2.27  tff(c_50, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.27  tff(c_198, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.88/2.27  tff(c_206, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_198])).
% 5.88/2.27  tff(c_46, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.88/2.27  tff(c_3031, plain, (![A_150, B_151]: (k4_xboole_0(A_150, k3_xboole_0(A_150, B_151))=k3_xboole_0(A_150, k4_xboole_0(A_150, B_151)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_225])).
% 5.88/2.27  tff(c_3125, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_3031])).
% 5.88/2.27  tff(c_3153, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3125])).
% 5.88/2.27  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.88/2.27  tff(c_899, plain, (![A_29, B_30, C_87]: (k4_xboole_0(A_29, k2_xboole_0(k4_xboole_0(A_29, B_30), C_87))=k4_xboole_0(k3_xboole_0(A_29, B_30), C_87))), inference(superposition, [status(thm), theory('equality')], [c_46, c_830])).
% 5.88/2.27  tff(c_105, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.88/2.27  tff(c_121, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_105, c_36])).
% 5.88/2.27  tff(c_341, plain, (![A_36]: (k4_xboole_0(k1_xboole_0, A_36)=k4_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_121, c_310])).
% 5.88/2.27  tff(c_361, plain, (![A_36]: (k4_xboole_0(k1_xboole_0, A_36)=k3_xboole_0(A_36, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_341])).
% 5.88/2.27  tff(c_574, plain, (![A_68, B_69]: (k4_xboole_0(k2_xboole_0(A_68, B_69), A_68)=k4_xboole_0(B_69, A_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_310])).
% 5.88/2.27  tff(c_616, plain, (![B_22, A_21]: (k4_xboole_0(k4_xboole_0(B_22, A_21), A_21)=k4_xboole_0(k2_xboole_0(A_21, B_22), A_21))), inference(superposition, [status(thm), theory('equality')], [c_38, c_574])).
% 5.88/2.27  tff(c_1048, plain, (![B_93, A_94]: (k4_xboole_0(k4_xboole_0(B_93, A_94), A_94)=k4_xboole_0(B_93, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_616])).
% 5.88/2.27  tff(c_1101, plain, (![A_36]: (k4_xboole_0(k3_xboole_0(A_36, k1_xboole_0), A_36)=k4_xboole_0(k1_xboole_0, A_36))), inference(superposition, [status(thm), theory('equality')], [c_361, c_1048])).
% 5.88/2.27  tff(c_1132, plain, (![A_36]: (k4_xboole_0(k3_xboole_0(A_36, k1_xboole_0), A_36)=k3_xboole_0(A_36, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_1101])).
% 5.88/2.27  tff(c_3694, plain, (![A_36]: (k4_xboole_0(k1_xboole_0, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3672, c_1132])).
% 5.88/2.27  tff(c_4103, plain, (![A_176, B_177, C_178]: (k4_xboole_0(A_176, k2_xboole_0(k4_xboole_0(A_176, B_177), C_178))=k4_xboole_0(k3_xboole_0(A_176, B_177), C_178))), inference(superposition, [status(thm), theory('equality')], [c_46, c_830])).
% 5.88/2.27  tff(c_4212, plain, (![A_23, C_178]: (k4_xboole_0(k3_xboole_0(A_23, k1_xboole_0), C_178)=k4_xboole_0(A_23, k2_xboole_0(A_23, C_178)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4103])).
% 5.88/2.27  tff(c_4299, plain, (![A_181, C_182]: (k4_xboole_0(A_181, k2_xboole_0(A_181, C_182))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3694, c_3672, c_4212])).
% 5.88/2.27  tff(c_4555, plain, (![B_187, A_188]: (k4_xboole_0(B_187, k2_xboole_0(A_188, B_187))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4299])).
% 5.88/2.27  tff(c_5819, plain, (![C_215, B_216]: (k4_xboole_0(k3_xboole_0(C_215, B_216), C_215)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_899, c_4555])).
% 5.88/2.27  tff(c_6144, plain, (![A_220, B_221]: (k4_xboole_0(k3_xboole_0(A_220, B_221), B_221)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_5819])).
% 5.88/2.27  tff(c_6236, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3153, c_6144])).
% 5.88/2.27  tff(c_335, plain, (![A_21, B_22]: (k4_xboole_0(k2_xboole_0(A_21, B_22), k4_xboole_0(B_22, A_21))=k4_xboole_0(A_21, k4_xboole_0(B_22, A_21)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_310])).
% 5.88/2.27  tff(c_6290, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6')))=k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6236, c_335])).
% 5.88/2.27  tff(c_6332, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4996, c_40, c_206, c_46, c_2, c_40, c_6290])).
% 5.88/2.27  tff(c_364, plain, (![A_61]: (k4_xboole_0(k1_xboole_0, A_61)=k3_xboole_0(A_61, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_341])).
% 5.88/2.27  tff(c_402, plain, (![B_30]: (k3_xboole_0(k4_xboole_0(k1_xboole_0, B_30), k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_30))), inference(superposition, [status(thm), theory('equality')], [c_46, c_364])).
% 5.88/2.27  tff(c_414, plain, (![B_30]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(B_30, k1_xboole_0))=k3_xboole_0(k1_xboole_0, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_361, c_402])).
% 5.88/2.27  tff(c_3692, plain, (![B_30]: (k3_xboole_0(k1_xboole_0, B_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3672, c_414])).
% 5.88/2.27  tff(c_52, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.27  tff(c_53, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 5.88/2.27  tff(c_190, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.88/2.27  tff(c_194, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_53, c_190])).
% 5.88/2.27  tff(c_338, plain, (k4_xboole_0(k2_xboole_0('#skF_6', '#skF_5'), k2_xboole_0('#skF_6', '#skF_5'))=k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_310])).
% 5.88/2.27  tff(c_360, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k3_xboole_0(k1_xboole_0, k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_246, c_338])).
% 5.88/2.27  tff(c_3791, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3692, c_360])).
% 5.88/2.27  tff(c_4923, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_6'))=k2_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3791, c_4867])).
% 5.88/2.27  tff(c_4994, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4923])).
% 5.88/2.27  tff(c_6345, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6332, c_4994])).
% 5.88/2.27  tff(c_4335, plain, (![A_181, C_182]: (k3_xboole_0(A_181, k2_xboole_0(A_181, C_182))=k4_xboole_0(A_181, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4299, c_46])).
% 5.88/2.27  tff(c_4787, plain, (![A_195, C_196]: (k3_xboole_0(A_195, k2_xboole_0(A_195, C_196))=A_195)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4335])).
% 5.88/2.27  tff(c_4831, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4787])).
% 5.88/2.27  tff(c_6470, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6345, c_4831])).
% 5.88/2.27  tff(c_516, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.88/2.27  tff(c_16, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, A_10) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.27  tff(c_6587, plain, (![A_222, B_223, B_224]: (r2_hidden('#skF_1'(k4_xboole_0(A_222, B_223), B_224), A_222) | r1_tarski(k4_xboole_0(A_222, B_223), B_224))), inference(resolution, [status(thm)], [c_516, c_16])).
% 5.88/2.27  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.88/2.27  tff(c_7120, plain, (![A_228, B_229]: (r1_tarski(k4_xboole_0(A_228, B_229), A_228))), inference(resolution, [status(thm)], [c_6587, c_8])).
% 5.88/2.27  tff(c_7216, plain, (![A_230, B_231]: (r1_tarski(k3_xboole_0(A_230, B_231), A_230))), inference(superposition, [status(thm), theory('equality')], [c_46, c_7120])).
% 5.88/2.27  tff(c_7272, plain, (![B_232, A_233]: (r1_tarski(k3_xboole_0(B_232, A_233), A_233))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7216])).
% 5.88/2.27  tff(c_7286, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6470, c_7272])).
% 5.88/2.27  tff(c_7320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_7286])).
% 5.88/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.27  
% 5.88/2.27  Inference rules
% 5.88/2.27  ----------------------
% 5.88/2.27  #Ref     : 0
% 5.88/2.27  #Sup     : 1735
% 5.88/2.27  #Fact    : 0
% 5.88/2.27  #Define  : 0
% 5.88/2.27  #Split   : 1
% 5.88/2.27  #Chain   : 0
% 5.88/2.27  #Close   : 0
% 5.88/2.27  
% 5.88/2.27  Ordering : KBO
% 5.88/2.27  
% 5.88/2.27  Simplification rules
% 5.88/2.27  ----------------------
% 5.88/2.27  #Subsume      : 184
% 5.88/2.27  #Demod        : 1531
% 5.88/2.27  #Tautology    : 896
% 5.88/2.27  #SimpNegUnit  : 1
% 5.88/2.27  #BackRed      : 31
% 5.88/2.27  
% 5.88/2.27  #Partial instantiations: 0
% 5.88/2.27  #Strategies tried      : 1
% 5.88/2.27  
% 5.88/2.27  Timing (in seconds)
% 5.88/2.27  ----------------------
% 5.88/2.27  Preprocessing        : 0.30
% 5.88/2.27  Parsing              : 0.17
% 5.88/2.27  CNF conversion       : 0.02
% 5.88/2.27  Main loop            : 1.16
% 5.88/2.27  Inferencing          : 0.34
% 5.88/2.27  Reduction            : 0.50
% 5.88/2.27  Demodulation         : 0.41
% 5.88/2.27  BG Simplification    : 0.04
% 5.88/2.27  Subsumption          : 0.20
% 5.88/2.27  Abstraction          : 0.05
% 5.88/2.27  MUC search           : 0.00
% 5.88/2.27  Cooper               : 0.00
% 5.88/2.27  Total                : 1.50
% 5.88/2.27  Index Insertion      : 0.00
% 5.88/2.27  Index Deletion       : 0.00
% 5.88/2.27  Index Matching       : 0.00
% 5.88/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
