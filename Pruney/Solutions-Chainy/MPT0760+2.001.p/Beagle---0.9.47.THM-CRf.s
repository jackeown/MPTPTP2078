%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:34 EST 2020

% Result     : Theorem 28.33s
% Output     : CNFRefutation 28.33s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 252 expanded)
%              Number of leaves         :   39 ( 103 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 414 expanded)
%              Number of equality atoms :   41 ( 154 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k1_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_72,plain,(
    k1_wellord1('#skF_11','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_76,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_925,plain,(
    ! [A_166,B_167,C_168] :
      ( r2_hidden('#skF_2'(A_166,B_167,C_168),A_166)
      | r2_hidden('#skF_3'(A_166,B_167,C_168),C_168)
      | k3_xboole_0(A_166,B_167) = C_168 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k3_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_995,plain,(
    ! [A_169,B_170] :
      ( r2_hidden('#skF_3'(A_169,B_170,A_169),A_169)
      | k3_xboole_0(A_169,B_170) = A_169 ) ),
    inference(resolution,[status(thm)],[c_925,c_22])).

tff(c_28,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_158,plain,(
    ! [D_73,A_74,B_75] :
      ( r2_hidden(D_73,A_74)
      | ~ r2_hidden(D_73,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_165,plain,(
    ! [D_73,A_14] :
      ( r2_hidden(D_73,A_14)
      | ~ r2_hidden(D_73,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_158])).

tff(c_1031,plain,(
    ! [B_171,A_172] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_171,k1_xboole_0),A_172)
      | k3_xboole_0(k1_xboole_0,B_171) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_995,c_165])).

tff(c_58,plain,(
    ! [D_54,A_43] :
      ( ~ r2_hidden(D_54,k1_wellord1(A_43,D_54))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1072,plain,(
    ! [A_43,B_171] :
      ( ~ v1_relat_1(A_43)
      | k3_xboole_0(k1_xboole_0,B_171) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1031,c_58])).

tff(c_1074,plain,(
    ! [A_43] : ~ v1_relat_1(A_43) ),
    inference(splitLeft,[status(thm)],[c_1072])).

tff(c_1076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1074,c_76])).

tff(c_1077,plain,(
    ! [B_171] : k3_xboole_0(k1_xboole_0,B_171) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1072])).

tff(c_26,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_2'(A_8,B_9,C_10),A_8)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k3_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_182,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_197,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_182])).

tff(c_205,plain,(
    ! [A_86] : k4_xboole_0(A_86,A_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_197])).

tff(c_34,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_210,plain,(
    ! [A_86] : k4_xboole_0(A_86,k1_xboole_0) = k3_xboole_0(A_86,A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_34])).

tff(c_222,plain,(
    ! [A_86] : k3_xboole_0(A_86,A_86) = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_210])).

tff(c_979,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_3'(A_166,B_167,A_166),A_166)
      | k3_xboole_0(A_166,B_167) = A_166 ) ),
    inference(resolution,[status(thm)],[c_925,c_22])).

tff(c_30,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_539,plain,(
    ! [A_123,C_124] :
      ( r2_hidden(k4_tarski('#skF_7'(A_123,k2_relat_1(A_123),C_124),C_124),A_123)
      | ~ r2_hidden(C_124,k2_relat_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    ! [B_42,A_41] :
      ( ~ r1_tarski(B_42,A_41)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2315,plain,(
    ! [A_267,C_268] :
      ( ~ r1_tarski(A_267,k4_tarski('#skF_7'(A_267,k2_relat_1(A_267),C_268),C_268))
      | ~ r2_hidden(C_268,k2_relat_1(A_267)) ) ),
    inference(resolution,[status(thm)],[c_539,c_52])).

tff(c_2351,plain,(
    ! [C_269] : ~ r2_hidden(C_269,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_30,c_2315])).

tff(c_2434,plain,(
    ! [B_167] : k3_xboole_0(k2_relat_1(k1_xboole_0),B_167) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_979,c_2351])).

tff(c_200,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_197])).

tff(c_2685,plain,(
    ! [B_279] : k3_xboole_0(k2_relat_1(k1_xboole_0),B_279) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_979,c_2351])).

tff(c_308,plain,(
    ! [A_99,B_100] : k4_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k3_xboole_0(A_99,k4_xboole_0(A_99,B_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_34])).

tff(c_314,plain,(
    ! [A_99,B_100] : k4_xboole_0(A_99,k3_xboole_0(A_99,k4_xboole_0(A_99,B_100))) = k3_xboole_0(A_99,k3_xboole_0(A_99,B_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_34])).

tff(c_2700,plain,(
    ! [B_100] : k3_xboole_0(k2_relat_1(k1_xboole_0),k3_xboole_0(k2_relat_1(k1_xboole_0),B_100)) = k4_xboole_0(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2685,c_314])).

tff(c_2754,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_2434,c_200,c_2700])).

tff(c_38,plain,(
    ! [A_21,C_36] :
      ( r2_hidden(k4_tarski('#skF_7'(A_21,k2_relat_1(A_21),C_36),C_36),A_21)
      | ~ r2_hidden(C_36,k2_relat_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2439,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_38,c_2351])).

tff(c_2860,plain,(
    ! [C_282] : ~ r2_hidden(C_282,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2754,c_2754,c_2439])).

tff(c_2902,plain,(
    ! [B_9,C_10] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_9,C_10),C_10)
      | k3_xboole_0(k1_xboole_0,B_9) = C_10 ) ),
    inference(resolution,[status(thm)],[c_26,c_2860])).

tff(c_3096,plain,(
    ! [B_293,C_294] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_293,C_294),C_294)
      | k1_xboole_0 = C_294 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_2902])).

tff(c_328,plain,(
    ! [D_101,B_102,A_103] :
      ( r2_hidden(k4_tarski(D_101,B_102),A_103)
      | ~ r2_hidden(D_101,k1_wellord1(A_103,B_102))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [C_36,A_21,D_39] :
      ( r2_hidden(C_36,k2_relat_1(A_21))
      | ~ r2_hidden(k4_tarski(D_39,C_36),A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_352,plain,(
    ! [B_102,A_103,D_101] :
      ( r2_hidden(B_102,k2_relat_1(A_103))
      | ~ r2_hidden(D_101,k1_wellord1(A_103,B_102))
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_328,c_40])).

tff(c_3141,plain,(
    ! [B_102,A_103] :
      ( r2_hidden(B_102,k2_relat_1(A_103))
      | ~ v1_relat_1(A_103)
      | k1_wellord1(A_103,B_102) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3096,c_352])).

tff(c_50,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k2_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_147,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_155,plain,(
    ! [A_70] : r1_tarski(A_70,A_70) ),
    inference(resolution,[status(thm)],[c_147,c_6])).

tff(c_96,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_111,plain,(
    ! [A_63,B_62] : r1_tarski(A_63,k2_xboole_0(B_62,A_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_36])).

tff(c_274,plain,(
    ! [D_94,A_95,B_96] :
      ( r2_hidden(D_94,k3_xboole_0(A_95,B_96))
      | ~ r2_hidden(D_94,B_96)
      | ~ r2_hidden(D_94,A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2959,plain,(
    ! [D_283,B_284,A_285,B_286] :
      ( r2_hidden(D_283,B_284)
      | ~ r1_tarski(k3_xboole_0(A_285,B_286),B_284)
      | ~ r2_hidden(D_283,B_286)
      | ~ r2_hidden(D_283,A_285) ) ),
    inference(resolution,[status(thm)],[c_274,c_4])).

tff(c_99891,plain,(
    ! [D_1274,B_1275,A_1276,B_1277] :
      ( r2_hidden(D_1274,k2_xboole_0(B_1275,k3_xboole_0(A_1276,B_1277)))
      | ~ r2_hidden(D_1274,B_1277)
      | ~ r2_hidden(D_1274,A_1276) ) ),
    inference(resolution,[status(thm)],[c_111,c_2959])).

tff(c_100191,plain,(
    ! [D_1278,B_1279,A_1280] :
      ( r2_hidden(D_1278,k2_xboole_0(B_1279,A_1280))
      | ~ r2_hidden(D_1278,A_1280)
      | ~ r2_hidden(D_1278,A_1280) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_99891])).

tff(c_113216,plain,(
    ! [D_1441,B_1442,B_1443,A_1444] :
      ( r2_hidden(D_1441,B_1442)
      | ~ r1_tarski(k2_xboole_0(B_1443,A_1444),B_1442)
      | ~ r2_hidden(D_1441,A_1444) ) ),
    inference(resolution,[status(thm)],[c_100191,c_4])).

tff(c_113255,plain,(
    ! [D_1445,B_1446,A_1447] :
      ( r2_hidden(D_1445,k2_xboole_0(B_1446,A_1447))
      | ~ r2_hidden(D_1445,A_1447) ) ),
    inference(resolution,[status(thm)],[c_155,c_113216])).

tff(c_115745,plain,(
    ! [D_1479,A_1480] :
      ( r2_hidden(D_1479,k3_relat_1(A_1480))
      | ~ r2_hidden(D_1479,k2_relat_1(A_1480))
      | ~ v1_relat_1(A_1480) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_113255])).

tff(c_74,plain,(
    ~ r2_hidden('#skF_10',k3_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_115908,plain,
    ( ~ r2_hidden('#skF_10',k2_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_115745,c_74])).

tff(c_115957,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_115908])).

tff(c_117380,plain,
    ( ~ v1_relat_1('#skF_11')
    | k1_wellord1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3141,c_115957])).

tff(c_117401,plain,(
    k1_wellord1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_117380])).

tff(c_117403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_117401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.33/18.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.33/18.74  
% 28.33/18.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.33/18.74  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k1_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_10 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 28.33/18.74  
% 28.33/18.74  %Foreground sorts:
% 28.33/18.74  
% 28.33/18.74  
% 28.33/18.74  %Background operators:
% 28.33/18.74  
% 28.33/18.74  
% 28.33/18.74  %Foreground operators:
% 28.33/18.74  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 28.33/18.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.33/18.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.33/18.74  tff('#skF_11', type, '#skF_11': $i).
% 28.33/18.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 28.33/18.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 28.33/18.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.33/18.74  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 28.33/18.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.33/18.74  tff('#skF_10', type, '#skF_10': $i).
% 28.33/18.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 28.33/18.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 28.33/18.74  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 28.33/18.74  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 28.33/18.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.33/18.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 28.33/18.74  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 28.33/18.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 28.33/18.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.33/18.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 28.33/18.74  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 28.33/18.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 28.33/18.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 28.33/18.74  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 28.33/18.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 28.33/18.74  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 28.33/18.74  
% 28.33/18.76  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord1)).
% 28.33/18.76  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 28.33/18.76  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 28.33/18.76  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 28.33/18.76  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 28.33/18.76  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 28.33/18.76  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 28.33/18.76  tff(f_61, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 28.33/18.76  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 28.33/18.76  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 28.33/18.76  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 28.33/18.76  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 28.33/18.76  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 28.33/18.76  tff(c_72, plain, (k1_wellord1('#skF_11', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 28.33/18.76  tff(c_76, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_90])).
% 28.33/18.76  tff(c_925, plain, (![A_166, B_167, C_168]: (r2_hidden('#skF_2'(A_166, B_167, C_168), A_166) | r2_hidden('#skF_3'(A_166, B_167, C_168), C_168) | k3_xboole_0(A_166, B_167)=C_168)), inference(cnfTransformation, [status(thm)], [f_43])).
% 28.33/18.76  tff(c_22, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k3_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 28.33/18.76  tff(c_995, plain, (![A_169, B_170]: (r2_hidden('#skF_3'(A_169, B_170, A_169), A_169) | k3_xboole_0(A_169, B_170)=A_169)), inference(resolution, [status(thm)], [c_925, c_22])).
% 28.33/18.76  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 28.33/18.76  tff(c_158, plain, (![D_73, A_74, B_75]: (r2_hidden(D_73, A_74) | ~r2_hidden(D_73, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 28.33/18.76  tff(c_165, plain, (![D_73, A_14]: (r2_hidden(D_73, A_14) | ~r2_hidden(D_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_158])).
% 28.33/18.76  tff(c_1031, plain, (![B_171, A_172]: (r2_hidden('#skF_3'(k1_xboole_0, B_171, k1_xboole_0), A_172) | k3_xboole_0(k1_xboole_0, B_171)=k1_xboole_0)), inference(resolution, [status(thm)], [c_995, c_165])).
% 28.33/18.76  tff(c_58, plain, (![D_54, A_43]: (~r2_hidden(D_54, k1_wellord1(A_43, D_54)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.33/18.76  tff(c_1072, plain, (![A_43, B_171]: (~v1_relat_1(A_43) | k3_xboole_0(k1_xboole_0, B_171)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1031, c_58])).
% 28.33/18.76  tff(c_1074, plain, (![A_43]: (~v1_relat_1(A_43))), inference(splitLeft, [status(thm)], [c_1072])).
% 28.33/18.76  tff(c_1076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1074, c_76])).
% 28.33/18.76  tff(c_1077, plain, (![B_171]: (k3_xboole_0(k1_xboole_0, B_171)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_1072])).
% 28.33/18.76  tff(c_26, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_2'(A_8, B_9, C_10), A_8) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k3_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 28.33/18.76  tff(c_32, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 28.33/18.76  tff(c_182, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_51])).
% 28.33/18.76  tff(c_197, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_182])).
% 28.33/18.76  tff(c_205, plain, (![A_86]: (k4_xboole_0(A_86, A_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_197])).
% 28.33/18.76  tff(c_34, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 28.33/18.76  tff(c_210, plain, (![A_86]: (k4_xboole_0(A_86, k1_xboole_0)=k3_xboole_0(A_86, A_86))), inference(superposition, [status(thm), theory('equality')], [c_205, c_34])).
% 28.33/18.76  tff(c_222, plain, (![A_86]: (k3_xboole_0(A_86, A_86)=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_210])).
% 28.33/18.76  tff(c_979, plain, (![A_166, B_167]: (r2_hidden('#skF_3'(A_166, B_167, A_166), A_166) | k3_xboole_0(A_166, B_167)=A_166)), inference(resolution, [status(thm)], [c_925, c_22])).
% 28.33/18.76  tff(c_30, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.33/18.76  tff(c_539, plain, (![A_123, C_124]: (r2_hidden(k4_tarski('#skF_7'(A_123, k2_relat_1(A_123), C_124), C_124), A_123) | ~r2_hidden(C_124, k2_relat_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 28.33/18.76  tff(c_52, plain, (![B_42, A_41]: (~r1_tarski(B_42, A_41) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_70])).
% 28.33/18.76  tff(c_2315, plain, (![A_267, C_268]: (~r1_tarski(A_267, k4_tarski('#skF_7'(A_267, k2_relat_1(A_267), C_268), C_268)) | ~r2_hidden(C_268, k2_relat_1(A_267)))), inference(resolution, [status(thm)], [c_539, c_52])).
% 28.33/18.76  tff(c_2351, plain, (![C_269]: (~r2_hidden(C_269, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_30, c_2315])).
% 28.33/18.76  tff(c_2434, plain, (![B_167]: (k3_xboole_0(k2_relat_1(k1_xboole_0), B_167)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_979, c_2351])).
% 28.33/18.76  tff(c_200, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_197])).
% 28.33/18.76  tff(c_2685, plain, (![B_279]: (k3_xboole_0(k2_relat_1(k1_xboole_0), B_279)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_979, c_2351])).
% 28.33/18.76  tff(c_308, plain, (![A_99, B_100]: (k4_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k3_xboole_0(A_99, k4_xboole_0(A_99, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_182, c_34])).
% 28.33/18.76  tff(c_314, plain, (![A_99, B_100]: (k4_xboole_0(A_99, k3_xboole_0(A_99, k4_xboole_0(A_99, B_100)))=k3_xboole_0(A_99, k3_xboole_0(A_99, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_308, c_34])).
% 28.33/18.76  tff(c_2700, plain, (![B_100]: (k3_xboole_0(k2_relat_1(k1_xboole_0), k3_xboole_0(k2_relat_1(k1_xboole_0), B_100))=k4_xboole_0(k2_relat_1(k1_xboole_0), k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_2685, c_314])).
% 28.33/18.76  tff(c_2754, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_222, c_2434, c_200, c_2700])).
% 28.33/18.76  tff(c_38, plain, (![A_21, C_36]: (r2_hidden(k4_tarski('#skF_7'(A_21, k2_relat_1(A_21), C_36), C_36), A_21) | ~r2_hidden(C_36, k2_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 28.33/18.76  tff(c_2439, plain, (![C_36]: (~r2_hidden(C_36, k2_relat_1(k2_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_38, c_2351])).
% 28.33/18.76  tff(c_2860, plain, (![C_282]: (~r2_hidden(C_282, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2754, c_2754, c_2439])).
% 28.33/18.76  tff(c_2902, plain, (![B_9, C_10]: (r2_hidden('#skF_3'(k1_xboole_0, B_9, C_10), C_10) | k3_xboole_0(k1_xboole_0, B_9)=C_10)), inference(resolution, [status(thm)], [c_26, c_2860])).
% 28.33/18.76  tff(c_3096, plain, (![B_293, C_294]: (r2_hidden('#skF_3'(k1_xboole_0, B_293, C_294), C_294) | k1_xboole_0=C_294)), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_2902])).
% 28.33/18.76  tff(c_328, plain, (![D_101, B_102, A_103]: (r2_hidden(k4_tarski(D_101, B_102), A_103) | ~r2_hidden(D_101, k1_wellord1(A_103, B_102)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_83])).
% 28.33/18.76  tff(c_40, plain, (![C_36, A_21, D_39]: (r2_hidden(C_36, k2_relat_1(A_21)) | ~r2_hidden(k4_tarski(D_39, C_36), A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 28.33/18.76  tff(c_352, plain, (![B_102, A_103, D_101]: (r2_hidden(B_102, k2_relat_1(A_103)) | ~r2_hidden(D_101, k1_wellord1(A_103, B_102)) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_328, c_40])).
% 28.33/18.76  tff(c_3141, plain, (![B_102, A_103]: (r2_hidden(B_102, k2_relat_1(A_103)) | ~v1_relat_1(A_103) | k1_wellord1(A_103, B_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3096, c_352])).
% 28.33/18.76  tff(c_50, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k2_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 28.33/18.76  tff(c_147, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_34])).
% 28.33/18.76  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 28.33/18.76  tff(c_155, plain, (![A_70]: (r1_tarski(A_70, A_70))), inference(resolution, [status(thm)], [c_147, c_6])).
% 28.33/18.76  tff(c_96, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 28.33/18.76  tff(c_36, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 28.33/18.76  tff(c_111, plain, (![A_63, B_62]: (r1_tarski(A_63, k2_xboole_0(B_62, A_63)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_36])).
% 28.33/18.76  tff(c_274, plain, (![D_94, A_95, B_96]: (r2_hidden(D_94, k3_xboole_0(A_95, B_96)) | ~r2_hidden(D_94, B_96) | ~r2_hidden(D_94, A_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 28.33/18.76  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 28.33/18.76  tff(c_2959, plain, (![D_283, B_284, A_285, B_286]: (r2_hidden(D_283, B_284) | ~r1_tarski(k3_xboole_0(A_285, B_286), B_284) | ~r2_hidden(D_283, B_286) | ~r2_hidden(D_283, A_285))), inference(resolution, [status(thm)], [c_274, c_4])).
% 28.33/18.76  tff(c_99891, plain, (![D_1274, B_1275, A_1276, B_1277]: (r2_hidden(D_1274, k2_xboole_0(B_1275, k3_xboole_0(A_1276, B_1277))) | ~r2_hidden(D_1274, B_1277) | ~r2_hidden(D_1274, A_1276))), inference(resolution, [status(thm)], [c_111, c_2959])).
% 28.33/18.76  tff(c_100191, plain, (![D_1278, B_1279, A_1280]: (r2_hidden(D_1278, k2_xboole_0(B_1279, A_1280)) | ~r2_hidden(D_1278, A_1280) | ~r2_hidden(D_1278, A_1280))), inference(superposition, [status(thm), theory('equality')], [c_222, c_99891])).
% 28.33/18.76  tff(c_113216, plain, (![D_1441, B_1442, B_1443, A_1444]: (r2_hidden(D_1441, B_1442) | ~r1_tarski(k2_xboole_0(B_1443, A_1444), B_1442) | ~r2_hidden(D_1441, A_1444))), inference(resolution, [status(thm)], [c_100191, c_4])).
% 28.33/18.76  tff(c_113255, plain, (![D_1445, B_1446, A_1447]: (r2_hidden(D_1445, k2_xboole_0(B_1446, A_1447)) | ~r2_hidden(D_1445, A_1447))), inference(resolution, [status(thm)], [c_155, c_113216])).
% 28.33/18.76  tff(c_115745, plain, (![D_1479, A_1480]: (r2_hidden(D_1479, k3_relat_1(A_1480)) | ~r2_hidden(D_1479, k2_relat_1(A_1480)) | ~v1_relat_1(A_1480))), inference(superposition, [status(thm), theory('equality')], [c_50, c_113255])).
% 28.33/18.76  tff(c_74, plain, (~r2_hidden('#skF_10', k3_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 28.33/18.76  tff(c_115908, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_115745, c_74])).
% 28.33/18.76  tff(c_115957, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_115908])).
% 28.33/18.76  tff(c_117380, plain, (~v1_relat_1('#skF_11') | k1_wellord1('#skF_11', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_3141, c_115957])).
% 28.33/18.76  tff(c_117401, plain, (k1_wellord1('#skF_11', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_76, c_117380])).
% 28.33/18.76  tff(c_117403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_117401])).
% 28.33/18.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.33/18.76  
% 28.33/18.76  Inference rules
% 28.33/18.76  ----------------------
% 28.33/18.76  #Ref     : 0
% 28.33/18.76  #Sup     : 29434
% 28.33/18.76  #Fact    : 0
% 28.33/18.76  #Define  : 0
% 28.33/18.76  #Split   : 5
% 28.33/18.76  #Chain   : 0
% 28.33/18.76  #Close   : 0
% 28.33/18.76  
% 28.33/18.76  Ordering : KBO
% 28.33/18.76  
% 28.33/18.76  Simplification rules
% 28.33/18.76  ----------------------
% 28.33/18.76  #Subsume      : 8695
% 28.33/18.76  #Demod        : 15955
% 28.33/18.76  #Tautology    : 8099
% 28.33/18.76  #SimpNegUnit  : 817
% 28.33/18.76  #BackRed      : 20
% 28.33/18.76  
% 28.33/18.76  #Partial instantiations: 0
% 28.33/18.76  #Strategies tried      : 1
% 28.33/18.76  
% 28.33/18.76  Timing (in seconds)
% 28.33/18.76  ----------------------
% 28.33/18.76  Preprocessing        : 0.31
% 28.33/18.76  Parsing              : 0.16
% 28.33/18.76  CNF conversion       : 0.03
% 28.33/18.76  Main loop            : 17.64
% 28.33/18.76  Inferencing          : 2.59
% 28.33/18.76  Reduction            : 4.12
% 28.33/18.76  Demodulation         : 2.72
% 28.33/18.76  BG Simplification    : 0.38
% 28.33/18.76  Subsumption          : 9.56
% 28.33/18.76  Abstraction          : 0.58
% 28.33/18.76  MUC search           : 0.00
% 28.33/18.76  Cooper               : 0.00
% 28.33/18.76  Total                : 17.99
% 28.33/18.76  Index Insertion      : 0.00
% 28.33/18.76  Index Deletion       : 0.00
% 28.33/18.76  Index Matching       : 0.00
% 28.33/18.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
