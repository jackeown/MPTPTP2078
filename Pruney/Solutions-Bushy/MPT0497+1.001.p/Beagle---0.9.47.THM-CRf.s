%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0497+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:24 EST 2020

% Result     : Theorem 24.25s
% Output     : CNFRefutation 24.34s
% Verified   : 
% Statistics : Number of formulae       :  139 (2727 expanded)
%              Number of leaves         :   34 ( 908 expanded)
%              Depth                    :   24
%              Number of atoms          :  249 (5794 expanded)
%              Number of equality atoms :   65 (1547 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_30,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_70,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_4,plain,(
    ! [B_3,A_2] : k3_xboole_0(B_3,A_2) = k3_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_77037,plain,(
    ! [A_972,B_973] :
      ( r1_xboole_0(A_972,B_973)
      | k3_xboole_0(A_972,B_973) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,
    ( k7_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_127,plain,(
    r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_70,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11')
    | k7_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_191,plain,(
    k7_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_70])).

tff(c_68,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_77,plain,(
    ! [A_58] :
      ( v1_relat_1(A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_81,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60,c_77])).

tff(c_4089,plain,(
    ! [A_235,B_236,C_237] :
      ( r2_hidden('#skF_1'(A_235,B_236,C_237),B_236)
      | r2_hidden(k4_tarski('#skF_3'(A_235,B_236,C_237),'#skF_4'(A_235,B_236,C_237)),C_237)
      | k7_relat_1(A_235,B_236) = C_237
      | ~ v1_relat_1(C_237)
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_690,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_hidden('#skF_9'(A_139,B_140,C_141),A_139)
      | r2_hidden('#skF_10'(A_139,B_140,C_141),C_141)
      | k3_xboole_0(A_139,B_140) = C_141 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r2_hidden('#skF_9'(A_42,B_43,C_44),C_44)
      | r2_hidden('#skF_10'(A_42,B_43,C_44),C_44)
      | k3_xboole_0(A_42,B_43) = C_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_898,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_10'(A_142,B_143,A_142),A_142)
      | k3_xboole_0(A_142,B_143) = A_142 ) ),
    inference(resolution,[status(thm)],[c_690,c_48])).

tff(c_296,plain,(
    ! [C_95,A_96] :
      ( r2_hidden(k4_tarski(C_95,'#skF_8'(A_96,k1_relat_1(A_96),C_95)),A_96)
      | ~ r2_hidden(C_95,k1_relat_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_151,plain,(
    k3_xboole_0(k1_relat_1('#skF_12'),'#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_127,c_139])).

tff(c_168,plain,(
    ! [D_72,B_73,A_74] :
      ( r2_hidden(D_72,B_73)
      | ~ r2_hidden(D_72,k3_xboole_0(A_74,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_171,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,'#skF_11')
      | ~ r2_hidden(D_72,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_168])).

tff(c_321,plain,(
    ! [C_95] :
      ( r2_hidden(k4_tarski(C_95,'#skF_8'(k1_xboole_0,k1_relat_1(k1_xboole_0),C_95)),'#skF_11')
      | ~ r2_hidden(C_95,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_296,c_171])).

tff(c_24,plain,(
    ! [C_38,A_23] :
      ( r2_hidden(k4_tarski(C_38,'#skF_8'(A_23,k1_relat_1(A_23),C_38)),A_23)
      | ~ r2_hidden(C_38,k1_relat_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    ! [B_55,A_54] :
      ( r1_xboole_0(B_55,A_54)
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_130,plain,(
    r1_xboole_0('#skF_11',k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_127,c_64])).

tff(c_150,plain,(
    k3_xboole_0('#skF_11',k1_relat_1('#skF_12')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_139])).

tff(c_38,plain,(
    ! [D_47,B_43,A_42] :
      ( r2_hidden(D_47,B_43)
      | ~ r2_hidden(D_47,k3_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_184,plain,(
    ! [D_47] :
      ( r2_hidden(D_47,k1_relat_1('#skF_12'))
      | ~ r2_hidden(D_47,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_38])).

tff(c_248,plain,(
    ! [D_89,A_90,B_91] :
      ( r2_hidden(D_89,k3_xboole_0(A_90,B_91))
      | ~ r2_hidden(D_89,B_91)
      | ~ r2_hidden(D_89,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_66,plain,(
    ! [B_57,A_56] :
      ( ~ v1_xboole_0(B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_281,plain,(
    ! [A_92,B_93,D_94] :
      ( ~ v1_xboole_0(k3_xboole_0(A_92,B_93))
      | ~ r2_hidden(D_94,B_93)
      | ~ r2_hidden(D_94,A_92) ) ),
    inference(resolution,[status(thm)],[c_248,c_66])).

tff(c_285,plain,(
    ! [D_94] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_94,'#skF_11')
      | ~ r2_hidden(D_94,k1_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_281])).

tff(c_351,plain,(
    ! [D_102] :
      ( ~ r2_hidden(D_102,'#skF_11')
      | ~ r2_hidden(D_102,k1_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_285])).

tff(c_361,plain,(
    ! [D_103] :
      ( ~ r2_hidden(D_103,'#skF_11')
      | ~ r2_hidden(D_103,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_184,c_351])).

tff(c_552,plain,(
    ! [C_126] :
      ( ~ r2_hidden(k4_tarski(C_126,'#skF_8'(k1_xboole_0,k1_relat_1(k1_xboole_0),C_126)),'#skF_11')
      | ~ r2_hidden(C_126,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_24,c_361])).

tff(c_556,plain,(
    ! [C_95] : ~ r2_hidden(C_95,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_321,c_552])).

tff(c_1535,plain,(
    ! [B_159] : k3_xboole_0(k1_relat_1(k1_xboole_0),B_159) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_898,c_556])).

tff(c_1003,plain,(
    ! [A_144,B_145] :
      ( ~ v1_xboole_0(A_144)
      | k3_xboole_0(A_144,B_145) = A_144 ) ),
    inference(resolution,[status(thm)],[c_898,c_66])).

tff(c_1007,plain,(
    ! [B_146] : k3_xboole_0(k1_xboole_0,B_146) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_1003])).

tff(c_1025,plain,(
    ! [B_146] : k3_xboole_0(B_146,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_4])).

tff(c_1540,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1535,c_1025])).

tff(c_578,plain,(
    ! [C_130] : ~ r2_hidden(C_130,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_321,c_552])).

tff(c_589,plain,(
    ! [C_131] : ~ r2_hidden(C_131,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_24,c_578])).

tff(c_599,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))) ),
    inference(resolution,[status(thm)],[c_24,c_589])).

tff(c_1593,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1540,c_1540,c_599])).

tff(c_4101,plain,(
    ! [A_235,B_236] :
      ( r2_hidden('#skF_1'(A_235,B_236,k1_xboole_0),B_236)
      | k7_relat_1(A_235,B_236) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_235) ) ),
    inference(resolution,[status(thm)],[c_4089,c_1593])).

tff(c_4152,plain,(
    ! [A_235,B_236] :
      ( r2_hidden('#skF_1'(A_235,B_236,k1_xboole_0),B_236)
      | k7_relat_1(A_235,B_236) = k1_xboole_0
      | ~ v1_relat_1(A_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4101])).

tff(c_9362,plain,(
    ! [C_397,A_398,B_399] :
      ( ~ v1_xboole_0(C_397)
      | r2_hidden('#skF_1'(A_398,B_399,C_397),B_399)
      | k7_relat_1(A_398,B_399) = C_397
      | ~ v1_relat_1(C_397)
      | ~ v1_relat_1(A_398) ) ),
    inference(resolution,[status(thm)],[c_4089,c_66])).

tff(c_9427,plain,(
    ! [C_400,A_401] :
      ( ~ v1_xboole_0(C_400)
      | k7_relat_1(A_401,k1_xboole_0) = C_400
      | ~ v1_relat_1(C_400)
      | ~ v1_relat_1(A_401) ) ),
    inference(resolution,[status(thm)],[c_9362,c_1593])).

tff(c_9429,plain,(
    ! [A_401] :
      ( k7_relat_1(A_401,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_401) ) ),
    inference(resolution,[status(thm)],[c_60,c_9427])).

tff(c_9433,plain,(
    ! [A_402] :
      ( k7_relat_1(A_402,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_402) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_9429])).

tff(c_9445,plain,(
    k7_relat_1('#skF_12',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_9433])).

tff(c_4177,plain,(
    ! [A_239,B_240,C_241] :
      ( r2_hidden(k4_tarski('#skF_1'(A_239,B_240,C_241),'#skF_2'(A_239,B_240,C_241)),A_239)
      | r2_hidden(k4_tarski('#skF_3'(A_239,B_240,C_241),'#skF_4'(A_239,B_240,C_241)),C_241)
      | k7_relat_1(A_239,B_240) = C_241
      | ~ v1_relat_1(C_241)
      | ~ v1_relat_1(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [D_21,B_15,E_22,A_4] :
      ( r2_hidden(D_21,B_15)
      | ~ r2_hidden(k4_tarski(D_21,E_22),k7_relat_1(A_4,B_15))
      | ~ v1_relat_1(k7_relat_1(A_4,B_15))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63746,plain,(
    ! [A_876,B_877,A_878,B_879] :
      ( r2_hidden('#skF_3'(A_876,B_877,k7_relat_1(A_878,B_879)),B_879)
      | ~ v1_relat_1(A_878)
      | r2_hidden(k4_tarski('#skF_1'(A_876,B_877,k7_relat_1(A_878,B_879)),'#skF_2'(A_876,B_877,k7_relat_1(A_878,B_879))),A_876)
      | k7_relat_1(A_878,B_879) = k7_relat_1(A_876,B_877)
      | ~ v1_relat_1(k7_relat_1(A_878,B_879))
      | ~ v1_relat_1(A_876) ) ),
    inference(resolution,[status(thm)],[c_4177,c_22])).

tff(c_63946,plain,(
    ! [A_876,B_877] :
      ( r2_hidden('#skF_3'(A_876,B_877,k7_relat_1('#skF_12',k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1('#skF_12')
      | r2_hidden(k4_tarski('#skF_1'(A_876,B_877,k1_xboole_0),'#skF_2'(A_876,B_877,k7_relat_1('#skF_12',k1_xboole_0))),A_876)
      | k7_relat_1(A_876,B_877) = k7_relat_1('#skF_12',k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1('#skF_12',k1_xboole_0))
      | ~ v1_relat_1(A_876) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9445,c_63746])).

tff(c_64001,plain,(
    ! [A_876,B_877] :
      ( r2_hidden('#skF_3'(A_876,B_877,k1_xboole_0),k1_xboole_0)
      | r2_hidden(k4_tarski('#skF_1'(A_876,B_877,k1_xboole_0),'#skF_2'(A_876,B_877,k1_xboole_0)),A_876)
      | k7_relat_1(A_876,B_877) = k1_xboole_0
      | ~ v1_relat_1(A_876) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_9445,c_9445,c_9445,c_68,c_9445,c_63946])).

tff(c_66557,plain,(
    ! [A_898,B_899] :
      ( r2_hidden(k4_tarski('#skF_1'(A_898,B_899,k1_xboole_0),'#skF_2'(A_898,B_899,k1_xboole_0)),A_898)
      | k7_relat_1(A_898,B_899) = k1_xboole_0
      | ~ v1_relat_1(A_898) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1593,c_64001])).

tff(c_26,plain,(
    ! [C_38,A_23,D_41] :
      ( r2_hidden(C_38,k1_relat_1(A_23))
      | ~ r2_hidden(k4_tarski(C_38,D_41),A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76539,plain,(
    ! [A_967,B_968] :
      ( r2_hidden('#skF_1'(A_967,B_968,k1_xboole_0),k1_relat_1(A_967))
      | k7_relat_1(A_967,B_968) = k1_xboole_0
      | ~ v1_relat_1(A_967) ) ),
    inference(resolution,[status(thm)],[c_66557,c_26])).

tff(c_295,plain,(
    ! [D_94] :
      ( ~ r2_hidden(D_94,'#skF_11')
      | ~ r2_hidden(D_94,k1_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_285])).

tff(c_76659,plain,(
    ! [B_968] :
      ( ~ r2_hidden('#skF_1'('#skF_12',B_968,k1_xboole_0),'#skF_11')
      | k7_relat_1('#skF_12',B_968) = k1_xboole_0
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_76539,c_295])).

tff(c_77010,plain,(
    ! [B_971] :
      ( ~ r2_hidden('#skF_1'('#skF_12',B_971,k1_xboole_0),'#skF_11')
      | k7_relat_1('#skF_12',B_971) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_76659])).

tff(c_77016,plain,
    ( k7_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_4152,c_77010])).

tff(c_77023,plain,(
    k7_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_77016])).

tff(c_77025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_77023])).

tff(c_77027,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_77040,plain,(
    k3_xboole_0(k1_relat_1('#skF_12'),'#skF_11') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77037,c_77027])).

tff(c_77044,plain,(
    k3_xboole_0('#skF_11',k1_relat_1('#skF_12')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_77040])).

tff(c_77283,plain,(
    ! [A_1025,B_1026,C_1027] :
      ( r2_hidden('#skF_9'(A_1025,B_1026,C_1027),B_1026)
      | r2_hidden('#skF_10'(A_1025,B_1026,C_1027),C_1027)
      | k3_xboole_0(A_1025,B_1026) = C_1027 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77417,plain,(
    ! [A_1028,B_1029] :
      ( r2_hidden('#skF_10'(A_1028,B_1029,B_1029),B_1029)
      | k3_xboole_0(A_1028,B_1029) = B_1029 ) ),
    inference(resolution,[status(thm)],[c_77283,c_48])).

tff(c_77128,plain,(
    ! [C_995,A_996] :
      ( r2_hidden(k4_tarski(C_995,'#skF_8'(A_996,k1_relat_1(A_996),C_995)),A_996)
      | ~ r2_hidden(C_995,k1_relat_1(A_996)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77146,plain,(
    ! [A_996,C_995] :
      ( ~ v1_xboole_0(A_996)
      | ~ r2_hidden(C_995,k1_relat_1(A_996)) ) ),
    inference(resolution,[status(thm)],[c_77128,c_66])).

tff(c_77928,plain,(
    ! [A_1050,A_1051] :
      ( ~ v1_xboole_0(A_1050)
      | k3_xboole_0(A_1051,k1_relat_1(A_1050)) = k1_relat_1(A_1050) ) ),
    inference(resolution,[status(thm)],[c_77417,c_77146])).

tff(c_77482,plain,(
    ! [B_1030,A_1031] :
      ( ~ v1_xboole_0(B_1030)
      | k3_xboole_0(A_1031,B_1030) = B_1030 ) ),
    inference(resolution,[status(thm)],[c_77417,c_66])).

tff(c_77620,plain,(
    ! [A_1035] : k3_xboole_0(A_1035,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_77482])).

tff(c_77051,plain,(
    ! [B_976,A_977] :
      ( r1_xboole_0(B_976,A_977)
      | k3_xboole_0(A_977,B_976) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_77037,c_64])).

tff(c_54,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_77060,plain,(
    ! [B_976,A_977] :
      ( k3_xboole_0(B_976,A_977) = k1_xboole_0
      | k3_xboole_0(A_977,B_976) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_77051,c_54])).

tff(c_77663,plain,(
    ! [A_1035] : k3_xboole_0(k1_xboole_0,A_1035) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77620,c_77060])).

tff(c_77984,plain,(
    ! [A_1052] :
      ( k1_relat_1(A_1052) = k1_xboole_0
      | ~ v1_xboole_0(A_1052) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77928,c_77663])).

tff(c_77988,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_77984])).

tff(c_34,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(k4_tarski('#skF_5'(A_23,B_24),'#skF_6'(A_23,B_24)),A_23)
      | r2_hidden('#skF_7'(A_23,B_24),B_24)
      | k1_relat_1(A_23) = B_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77162,plain,(
    ! [A_999,C_1000] :
      ( ~ v1_xboole_0(A_999)
      | ~ r2_hidden(C_1000,k1_relat_1(A_999)) ) ),
    inference(resolution,[status(thm)],[c_77128,c_66])).

tff(c_77173,plain,(
    ! [A_1001,C_1002] :
      ( ~ v1_xboole_0(A_1001)
      | ~ r2_hidden(C_1002,k1_relat_1(k1_relat_1(A_1001))) ) ),
    inference(resolution,[status(thm)],[c_24,c_77162])).

tff(c_77184,plain,(
    ! [A_1003,C_1004] :
      ( ~ v1_xboole_0(A_1003)
      | ~ r2_hidden(C_1004,k1_relat_1(k1_relat_1(k1_relat_1(A_1003)))) ) ),
    inference(resolution,[status(thm)],[c_24,c_77173])).

tff(c_77195,plain,(
    ! [A_1005,C_1006] :
      ( ~ v1_xboole_0(A_1005)
      | ~ r2_hidden(C_1006,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1005))))) ) ),
    inference(resolution,[status(thm)],[c_24,c_77184])).

tff(c_77206,plain,(
    ! [A_1007,C_1008] :
      ( ~ v1_xboole_0(A_1007)
      | ~ r2_hidden(C_1008,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1007)))))) ) ),
    inference(resolution,[status(thm)],[c_24,c_77195])).

tff(c_77216,plain,(
    ! [A_1007,C_38] :
      ( ~ v1_xboole_0(A_1007)
      | ~ r2_hidden(C_38,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1007))))))) ) ),
    inference(resolution,[status(thm)],[c_24,c_77206])).

tff(c_78008,plain,(
    ! [C_38] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_38,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77988,c_77216])).

tff(c_78069,plain,(
    ! [C_1057] : ~ r2_hidden(C_1057,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77988,c_77988,c_77988,c_77988,c_77988,c_60,c_78008])).

tff(c_78073,plain,(
    ! [B_24] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_24),B_24)
      | k1_relat_1(k1_xboole_0) = B_24 ) ),
    inference(resolution,[status(thm)],[c_34,c_78069])).

tff(c_78191,plain,(
    ! [B_1062] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_1062),B_1062)
      | k1_xboole_0 = B_1062 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77988,c_78073])).

tff(c_40,plain,(
    ! [D_47,A_42,B_43] :
      ( r2_hidden(D_47,A_42)
      | ~ r2_hidden(D_47,k3_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84516,plain,(
    ! [A_1168,B_1169] :
      ( r2_hidden('#skF_7'(k1_xboole_0,k3_xboole_0(A_1168,B_1169)),A_1168)
      | k3_xboole_0(A_1168,B_1169) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_78191,c_40])).

tff(c_84620,plain,(
    ! [B_3,A_2] :
      ( r2_hidden('#skF_7'(k1_xboole_0,k3_xboole_0(B_3,A_2)),A_2)
      | k3_xboole_0(A_2,B_3) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_84516])).

tff(c_78040,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77988,c_77988,c_77988,c_77988,c_77988,c_60,c_78008])).

tff(c_77026,plain,(
    k7_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_78845,plain,(
    ! [D_1068,E_1069,A_1070,B_1071] :
      ( r2_hidden(k4_tarski(D_1068,E_1069),k7_relat_1(A_1070,B_1071))
      | ~ r2_hidden(k4_tarski(D_1068,E_1069),A_1070)
      | ~ r2_hidden(D_1068,B_1071)
      | ~ v1_relat_1(k7_relat_1(A_1070,B_1071))
      | ~ v1_relat_1(A_1070) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78863,plain,(
    ! [D_1068,E_1069] :
      ( r2_hidden(k4_tarski(D_1068,E_1069),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1068,E_1069),'#skF_12')
      | ~ r2_hidden(D_1068,'#skF_11')
      | ~ v1_relat_1(k7_relat_1('#skF_12','#skF_11'))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77026,c_78845])).

tff(c_78870,plain,(
    ! [D_1068,E_1069] :
      ( r2_hidden(k4_tarski(D_1068,E_1069),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1068,E_1069),'#skF_12')
      | ~ r2_hidden(D_1068,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_81,c_77026,c_78863])).

tff(c_78872,plain,(
    ! [D_1072,E_1073] :
      ( ~ r2_hidden(k4_tarski(D_1072,E_1073),'#skF_12')
      | ~ r2_hidden(D_1072,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78040,c_78870])).

tff(c_78882,plain,(
    ! [C_38] :
      ( ~ r2_hidden(C_38,'#skF_11')
      | ~ r2_hidden(C_38,k1_relat_1('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_24,c_78872])).

tff(c_84982,plain,(
    ! [B_1201] :
      ( ~ r2_hidden('#skF_7'(k1_xboole_0,k3_xboole_0(k1_relat_1('#skF_12'),B_1201)),'#skF_11')
      | k3_xboole_0(k1_relat_1('#skF_12'),B_1201) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_84516,c_78882])).

tff(c_84986,plain,
    ( k3_xboole_0(k1_relat_1('#skF_12'),'#skF_11') = k1_xboole_0
    | k3_xboole_0('#skF_11',k1_relat_1('#skF_12')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84620,c_84982])).

tff(c_85040,plain,
    ( k3_xboole_0('#skF_11',k1_relat_1('#skF_12')) = k1_xboole_0
    | k3_xboole_0('#skF_11',k1_relat_1('#skF_12')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_84986])).

tff(c_85042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77044,c_77044,c_85040])).

%------------------------------------------------------------------------------
