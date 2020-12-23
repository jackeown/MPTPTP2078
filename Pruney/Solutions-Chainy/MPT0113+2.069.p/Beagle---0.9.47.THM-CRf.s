%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:20 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 151 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 211 expanded)
%              Number of equality atoms :   45 (  85 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_1201,plain,(
    ! [A_107,B_108] :
      ( r1_xboole_0(A_107,B_108)
      | k3_xboole_0(A_107,B_108) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_71,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_50])).

tff(c_36,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_77,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_452,plain,(
    ! [A_73,B_74,C_75] : k2_xboole_0(k4_xboole_0(A_73,B_74),k3_xboole_0(A_73,C_75)) = k4_xboole_0(A_73,k4_xboole_0(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_963,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k4_xboole_0(A_95,B_96),k4_xboole_0(A_95,k4_xboole_0(B_96,C_97))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_26])).

tff(c_1041,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_963])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_155,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_2'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_160,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_155])).

tff(c_161,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_10,c_155])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_165,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_20])).

tff(c_286,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(A_61,k4_xboole_0(B_62,A_61)) = B_62
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_307,plain,(
    ! [A_52] :
      ( k2_xboole_0(A_52,k1_xboole_0) = A_52
      | ~ r1_tarski(A_52,A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_286])).

tff(c_323,plain,(
    ! [A_52] : k2_xboole_0(A_52,k1_xboole_0) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_307])).

tff(c_90,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_23] : k4_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    ! [B_42] : k3_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_30])).

tff(c_364,plain,(
    ! [A_66,B_67,C_68] : r1_tarski(k2_xboole_0(k3_xboole_0(A_66,B_67),k3_xboole_0(A_66,C_68)),k2_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_394,plain,(
    ! [C_68,B_42] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,C_68)),k2_xboole_0(B_42,C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_364])).

tff(c_401,plain,(
    ! [B_69,C_70] : r1_tarski(k1_xboole_0,k2_xboole_0(B_69,C_70)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_100,c_394])).

tff(c_406,plain,(
    ! [A_52] : r1_tarski(k1_xboole_0,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_401])).

tff(c_112,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_90])).

tff(c_28,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_485,plain,(
    ! [A_52,C_75] : k4_xboole_0(A_52,k4_xboole_0(A_52,C_75)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_52,C_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_452])).

tff(c_518,plain,(
    ! [A_77,C_78] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_77,C_78)) = k3_xboole_0(A_77,C_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_485])).

tff(c_539,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(A_19,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_518])).

tff(c_553,plain,(
    ! [A_79] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_79,k1_xboole_0)) = k4_xboole_0(A_79,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_539])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_562,plain,(
    ! [A_79] :
      ( k4_xboole_0(A_79,k1_xboole_0) = A_79
      | ~ r1_tarski(k1_xboole_0,A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_24])).

tff(c_589,plain,(
    ! [A_79] : k4_xboole_0(A_79,k1_xboole_0) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_562])).

tff(c_1142,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_589])).

tff(c_1160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1142])).

tff(c_1161,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1209,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1201,c_1161])).

tff(c_1256,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_2'(A_114,B_115),A_114)
      | r1_tarski(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1266,plain,(
    ! [A_116] : r1_tarski(A_116,A_116) ),
    inference(resolution,[status(thm)],[c_1256,c_8])).

tff(c_1270,plain,(
    ! [A_116] : k4_xboole_0(A_116,A_116) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1266,c_20])).

tff(c_1628,plain,(
    ! [A_141,B_142,C_143] : k2_xboole_0(k4_xboole_0(A_141,B_142),k3_xboole_0(A_141,C_143)) = k4_xboole_0(A_141,k4_xboole_0(B_142,C_143)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1673,plain,(
    ! [A_116,C_143] : k4_xboole_0(A_116,k4_xboole_0(A_116,C_143)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_116,C_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_1628])).

tff(c_1698,plain,(
    ! [A_116,C_143] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_116,C_143)) = k3_xboole_0(A_116,C_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1673])).

tff(c_1162,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1180,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k1_xboole_0
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1191,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1162,c_1180])).

tff(c_1685,plain,(
    ! [C_143] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_143)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1191,c_1628])).

tff(c_1857,plain,(
    ! [C_152] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_152)) = k3_xboole_0('#skF_3',C_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1698,c_1685])).

tff(c_1192,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1180])).

tff(c_1872,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1857,c_1192])).

tff(c_1901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1209,c_1872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.59  
% 3.54/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.54/1.59  
% 3.54/1.59  %Foreground sorts:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Background operators:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Foreground operators:
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.54/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.54/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.54/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.54/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.59  
% 3.54/1.61  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.54/1.61  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.54/1.61  tff(f_68, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.54/1.61  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.54/1.61  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.54/1.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.54/1.61  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.54/1.61  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.54/1.61  tff(f_59, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.54/1.61  tff(f_49, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.54/1.61  tff(c_1201, plain, (![A_107, B_108]: (r1_xboole_0(A_107, B_108) | k3_xboole_0(A_107, B_108)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.54/1.61  tff(c_67, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.61  tff(c_34, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.54/1.61  tff(c_50, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 3.54/1.61  tff(c_71, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_67, c_50])).
% 3.54/1.61  tff(c_36, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.54/1.61  tff(c_77, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.61  tff(c_85, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_77])).
% 3.54/1.61  tff(c_452, plain, (![A_73, B_74, C_75]: (k2_xboole_0(k4_xboole_0(A_73, B_74), k3_xboole_0(A_73, C_75))=k4_xboole_0(A_73, k4_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.61  tff(c_26, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.54/1.61  tff(c_963, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k4_xboole_0(A_95, B_96), k4_xboole_0(A_95, k4_xboole_0(B_96, C_97)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_452, c_26])).
% 3.54/1.61  tff(c_1041, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_85, c_963])).
% 3.54/1.61  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.54/1.61  tff(c_155, plain, (![A_50, B_51]: (~r2_hidden('#skF_2'(A_50, B_51), B_51) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.54/1.61  tff(c_160, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_155])).
% 3.54/1.61  tff(c_161, plain, (![A_52]: (r1_tarski(A_52, A_52))), inference(resolution, [status(thm)], [c_10, c_155])).
% 3.54/1.61  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.61  tff(c_165, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_161, c_20])).
% 3.54/1.61  tff(c_286, plain, (![A_61, B_62]: (k2_xboole_0(A_61, k4_xboole_0(B_62, A_61))=B_62 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.61  tff(c_307, plain, (![A_52]: (k2_xboole_0(A_52, k1_xboole_0)=A_52 | ~r1_tarski(A_52, A_52))), inference(superposition, [status(thm), theory('equality')], [c_165, c_286])).
% 3.54/1.61  tff(c_323, plain, (![A_52]: (k2_xboole_0(A_52, k1_xboole_0)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_307])).
% 3.54/1.61  tff(c_90, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.54/1.61  tff(c_30, plain, (![A_23]: (k4_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.54/1.61  tff(c_100, plain, (![B_42]: (k3_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_30])).
% 3.54/1.61  tff(c_364, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_66, B_67), k3_xboole_0(A_66, C_68)), k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.54/1.61  tff(c_394, plain, (![C_68, B_42]: (r1_tarski(k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, C_68)), k2_xboole_0(B_42, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_364])).
% 3.54/1.61  tff(c_401, plain, (![B_69, C_70]: (r1_tarski(k1_xboole_0, k2_xboole_0(B_69, C_70)))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_100, c_394])).
% 3.54/1.61  tff(c_406, plain, (![A_52]: (r1_tarski(k1_xboole_0, A_52))), inference(superposition, [status(thm), theory('equality')], [c_323, c_401])).
% 3.54/1.61  tff(c_112, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_90])).
% 3.54/1.61  tff(c_28, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.54/1.61  tff(c_485, plain, (![A_52, C_75]: (k4_xboole_0(A_52, k4_xboole_0(A_52, C_75))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_52, C_75)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_452])).
% 3.54/1.61  tff(c_518, plain, (![A_77, C_78]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_77, C_78))=k3_xboole_0(A_77, C_78))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_485])).
% 3.54/1.61  tff(c_539, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k2_xboole_0(k1_xboole_0, k4_xboole_0(A_19, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_518])).
% 3.54/1.61  tff(c_553, plain, (![A_79]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_79, k1_xboole_0))=k4_xboole_0(A_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_539])).
% 3.54/1.61  tff(c_24, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.61  tff(c_562, plain, (![A_79]: (k4_xboole_0(A_79, k1_xboole_0)=A_79 | ~r1_tarski(k1_xboole_0, A_79))), inference(superposition, [status(thm), theory('equality')], [c_553, c_24])).
% 3.54/1.61  tff(c_589, plain, (![A_79]: (k4_xboole_0(A_79, k1_xboole_0)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_406, c_562])).
% 3.54/1.61  tff(c_1142, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1041, c_589])).
% 3.54/1.61  tff(c_1160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_1142])).
% 3.54/1.61  tff(c_1161, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 3.54/1.61  tff(c_1209, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1201, c_1161])).
% 3.54/1.61  tff(c_1256, plain, (![A_114, B_115]: (r2_hidden('#skF_2'(A_114, B_115), A_114) | r1_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.54/1.61  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.54/1.61  tff(c_1266, plain, (![A_116]: (r1_tarski(A_116, A_116))), inference(resolution, [status(thm)], [c_1256, c_8])).
% 3.54/1.61  tff(c_1270, plain, (![A_116]: (k4_xboole_0(A_116, A_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1266, c_20])).
% 3.54/1.61  tff(c_1628, plain, (![A_141, B_142, C_143]: (k2_xboole_0(k4_xboole_0(A_141, B_142), k3_xboole_0(A_141, C_143))=k4_xboole_0(A_141, k4_xboole_0(B_142, C_143)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.61  tff(c_1673, plain, (![A_116, C_143]: (k4_xboole_0(A_116, k4_xboole_0(A_116, C_143))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_116, C_143)))), inference(superposition, [status(thm), theory('equality')], [c_1270, c_1628])).
% 3.54/1.61  tff(c_1698, plain, (![A_116, C_143]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_116, C_143))=k3_xboole_0(A_116, C_143))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1673])).
% 3.54/1.61  tff(c_1162, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 3.54/1.61  tff(c_1180, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k1_xboole_0 | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.61  tff(c_1191, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1162, c_1180])).
% 3.54/1.61  tff(c_1685, plain, (![C_143]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_143))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_143)))), inference(superposition, [status(thm), theory('equality')], [c_1191, c_1628])).
% 3.54/1.61  tff(c_1857, plain, (![C_152]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_152))=k3_xboole_0('#skF_3', C_152))), inference(demodulation, [status(thm), theory('equality')], [c_1698, c_1685])).
% 3.54/1.61  tff(c_1192, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1180])).
% 3.54/1.61  tff(c_1872, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1857, c_1192])).
% 3.54/1.61  tff(c_1901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1209, c_1872])).
% 3.54/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.61  
% 3.54/1.61  Inference rules
% 3.54/1.61  ----------------------
% 3.54/1.61  #Ref     : 0
% 3.54/1.61  #Sup     : 468
% 3.54/1.61  #Fact    : 0
% 3.54/1.61  #Define  : 0
% 3.54/1.61  #Split   : 5
% 3.54/1.61  #Chain   : 0
% 3.54/1.61  #Close   : 0
% 3.54/1.61  
% 3.54/1.61  Ordering : KBO
% 3.54/1.61  
% 3.54/1.61  Simplification rules
% 3.54/1.61  ----------------------
% 3.54/1.61  #Subsume      : 9
% 3.54/1.61  #Demod        : 212
% 3.54/1.61  #Tautology    : 257
% 3.54/1.61  #SimpNegUnit  : 2
% 3.54/1.61  #BackRed      : 8
% 3.54/1.61  
% 3.54/1.61  #Partial instantiations: 0
% 3.54/1.61  #Strategies tried      : 1
% 3.54/1.61  
% 3.54/1.61  Timing (in seconds)
% 3.54/1.61  ----------------------
% 3.54/1.61  Preprocessing        : 0.28
% 3.54/1.61  Parsing              : 0.15
% 3.54/1.61  CNF conversion       : 0.02
% 3.54/1.61  Main loop            : 0.56
% 3.54/1.61  Inferencing          : 0.22
% 3.54/1.61  Reduction            : 0.19
% 3.54/1.61  Demodulation         : 0.14
% 3.54/1.61  BG Simplification    : 0.03
% 3.54/1.61  Subsumption          : 0.08
% 3.54/1.61  Abstraction          : 0.03
% 3.54/1.61  MUC search           : 0.00
% 3.54/1.61  Cooper               : 0.00
% 3.54/1.61  Total                : 0.89
% 3.54/1.61  Index Insertion      : 0.00
% 3.54/1.61  Index Deletion       : 0.00
% 3.54/1.61  Index Matching       : 0.00
% 3.54/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
