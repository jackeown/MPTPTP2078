%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:52 EST 2020

% Result     : Theorem 14.66s
% Output     : CNFRefutation 14.66s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 168 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  101 ( 230 expanded)
%              Number of equality atoms :   44 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_164,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_168,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    ! [A_38] : k2_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_38])).

tff(c_620,plain,(
    ! [A_80,B_81] : k2_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_642,plain,(
    ! [B_81] : k4_xboole_0(B_81,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_92])).

tff(c_671,plain,(
    ! [B_81] : k4_xboole_0(B_81,k1_xboole_0) = B_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_642])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1474,plain,(
    ! [C_114,B_115,A_116] :
      ( r2_hidden(C_114,B_115)
      | ~ r2_hidden(C_114,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6504,plain,(
    ! [A_235,B_236,B_237] :
      ( r2_hidden('#skF_1'(A_235,B_236),B_237)
      | ~ r1_tarski(A_235,B_237)
      | r1_tarski(A_235,B_236) ) ),
    inference(resolution,[status(thm)],[c_8,c_1474])).

tff(c_65,plain,(
    ! [A_34,B_35] : r1_tarski(A_34,k2_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_68,plain,(
    ! [A_20] : r1_tarski(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_65])).

tff(c_262,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_285,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_262])).

tff(c_568,plain,(
    ! [D_70,B_71,A_72] :
      ( ~ r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k4_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_589,plain,(
    ! [D_73,A_74] :
      ( ~ r2_hidden(D_73,A_74)
      | ~ r2_hidden(D_73,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_568])).

tff(c_592,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),k1_xboole_0)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_589])).

tff(c_6541,plain,(
    ! [A_238,B_239] :
      ( ~ r1_tarski(A_238,k1_xboole_0)
      | r1_tarski(A_238,B_239) ) ),
    inference(resolution,[status(thm)],[c_6504,c_592])).

tff(c_6544,plain,(
    ! [A_16,B_239] :
      ( r1_tarski(A_16,B_239)
      | k4_xboole_0(A_16,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_6541])).

tff(c_6559,plain,(
    ! [A_240,B_241] :
      ( r1_tarski(A_240,B_241)
      | k1_xboole_0 != A_240 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_6544])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6725,plain,(
    ! [A_244,B_245] :
      ( k2_xboole_0(A_244,B_245) = B_245
      | k1_xboole_0 != A_244 ) ),
    inference(resolution,[status(thm)],[c_6559,c_36])).

tff(c_7385,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6725])).

tff(c_48,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_85,plain,(
    ! [A_38,B_37] : r1_tarski(A_38,k2_xboole_0(B_37,A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_48])).

tff(c_281,plain,(
    ! [A_38,B_37] : k4_xboole_0(A_38,k2_xboole_0(B_37,A_38)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_262])).

tff(c_2265,plain,(
    ! [A_130,B_131,C_132] : k4_xboole_0(k4_xboole_0(A_130,B_131),C_132) = k4_xboole_0(A_130,k2_xboole_0(B_131,C_132)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7748,plain,(
    ! [C_253,A_254,B_255] : k2_xboole_0(C_253,k4_xboole_0(A_254,k2_xboole_0(B_255,C_253))) = k2_xboole_0(C_253,k4_xboole_0(A_254,B_255)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2265,c_42])).

tff(c_7987,plain,(
    ! [A_38,B_37] : k2_xboole_0(A_38,k4_xboole_0(A_38,B_37)) = k2_xboole_0(A_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_7748])).

tff(c_8249,plain,(
    ! [A_256,B_257] : k2_xboole_0(A_256,k4_xboole_0(A_256,B_257)) = A_256 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7385,c_7987])).

tff(c_8527,plain,(
    ! [A_258,B_259] : r1_tarski(k4_xboole_0(A_258,B_259),A_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_8249,c_85])).

tff(c_52,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1358,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_xboole_0(A_104,C_105)
      | ~ r1_xboole_0(B_106,C_105)
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1365,plain,(
    ! [A_107] :
      ( r1_xboole_0(A_107,'#skF_6')
      | ~ r1_tarski(A_107,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_1358])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1372,plain,(
    ! [A_107] :
      ( k3_xboole_0(A_107,'#skF_6') = k1_xboole_0
      | ~ r1_tarski(A_107,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1365,c_28])).

tff(c_8615,plain,(
    ! [B_259] : k3_xboole_0(k4_xboole_0('#skF_4',B_259),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8527,c_1372])).

tff(c_54,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_55,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_284,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_262])).

tff(c_36715,plain,(
    ! [B_558,A_559,A_560] : k2_xboole_0(B_558,k4_xboole_0(A_559,k2_xboole_0(B_558,A_560))) = k2_xboole_0(B_558,k4_xboole_0(A_559,A_560)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7748])).

tff(c_37336,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_36715])).

tff(c_37473,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7385,c_37336])).

tff(c_346,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_365,plain,(
    ! [A_38,B_37] : k3_xboole_0(A_38,k2_xboole_0(B_37,A_38)) = A_38 ),
    inference(resolution,[status(thm)],[c_85,c_346])).

tff(c_37726,plain,(
    k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_6') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_37473,c_365])).

tff(c_37821,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8615,c_37726])).

tff(c_37823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_37821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:36:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.66/6.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.66/6.73  
% 14.66/6.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.66/6.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 14.66/6.73  
% 14.66/6.73  %Foreground sorts:
% 14.66/6.73  
% 14.66/6.73  
% 14.66/6.73  %Background operators:
% 14.66/6.73  
% 14.66/6.73  
% 14.66/6.73  %Foreground operators:
% 14.66/6.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.66/6.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.66/6.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.66/6.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.66/6.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.66/6.73  tff('#skF_5', type, '#skF_5': $i).
% 14.66/6.73  tff('#skF_6', type, '#skF_6': $i).
% 14.66/6.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.66/6.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.66/6.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.66/6.73  tff('#skF_4', type, '#skF_4': $i).
% 14.66/6.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.66/6.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.66/6.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.66/6.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.66/6.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.66/6.73  
% 14.66/6.75  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.66/6.75  tff(f_81, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 14.66/6.75  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.66/6.75  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 14.66/6.75  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.66/6.75  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.66/6.75  tff(f_74, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.66/6.75  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.66/6.75  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.66/6.75  tff(f_66, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.66/6.75  tff(f_72, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 14.66/6.75  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 14.66/6.75  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.66/6.75  tff(c_164, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | k4_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.66/6.75  tff(c_50, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.66/6.75  tff(c_168, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_164, c_50])).
% 14.66/6.75  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.66/6.75  tff(c_70, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.66/6.75  tff(c_38, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.66/6.75  tff(c_92, plain, (![A_38]: (k2_xboole_0(k1_xboole_0, A_38)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_70, c_38])).
% 14.66/6.75  tff(c_620, plain, (![A_80, B_81]: (k2_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.66/6.75  tff(c_642, plain, (![B_81]: (k4_xboole_0(B_81, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_81))), inference(superposition, [status(thm), theory('equality')], [c_620, c_92])).
% 14.66/6.75  tff(c_671, plain, (![B_81]: (k4_xboole_0(B_81, k1_xboole_0)=B_81)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_642])).
% 14.66/6.75  tff(c_32, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.66/6.75  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.66/6.75  tff(c_1474, plain, (![C_114, B_115, A_116]: (r2_hidden(C_114, B_115) | ~r2_hidden(C_114, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.66/6.75  tff(c_6504, plain, (![A_235, B_236, B_237]: (r2_hidden('#skF_1'(A_235, B_236), B_237) | ~r1_tarski(A_235, B_237) | r1_tarski(A_235, B_236))), inference(resolution, [status(thm)], [c_8, c_1474])).
% 14.66/6.75  tff(c_65, plain, (![A_34, B_35]: (r1_tarski(A_34, k2_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.66/6.75  tff(c_68, plain, (![A_20]: (r1_tarski(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_38, c_65])).
% 14.66/6.75  tff(c_262, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.66/6.75  tff(c_285, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_262])).
% 14.66/6.75  tff(c_568, plain, (![D_70, B_71, A_72]: (~r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k4_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.66/6.75  tff(c_589, plain, (![D_73, A_74]: (~r2_hidden(D_73, A_74) | ~r2_hidden(D_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_285, c_568])).
% 14.66/6.75  tff(c_592, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), k1_xboole_0) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_589])).
% 14.66/6.75  tff(c_6541, plain, (![A_238, B_239]: (~r1_tarski(A_238, k1_xboole_0) | r1_tarski(A_238, B_239))), inference(resolution, [status(thm)], [c_6504, c_592])).
% 14.66/6.75  tff(c_6544, plain, (![A_16, B_239]: (r1_tarski(A_16, B_239) | k4_xboole_0(A_16, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_6541])).
% 14.66/6.75  tff(c_6559, plain, (![A_240, B_241]: (r1_tarski(A_240, B_241) | k1_xboole_0!=A_240)), inference(demodulation, [status(thm), theory('equality')], [c_671, c_6544])).
% 14.66/6.75  tff(c_36, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.66/6.75  tff(c_6725, plain, (![A_244, B_245]: (k2_xboole_0(A_244, B_245)=B_245 | k1_xboole_0!=A_244)), inference(resolution, [status(thm)], [c_6559, c_36])).
% 14.66/6.75  tff(c_7385, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6725])).
% 14.66/6.75  tff(c_48, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.66/6.75  tff(c_85, plain, (![A_38, B_37]: (r1_tarski(A_38, k2_xboole_0(B_37, A_38)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_48])).
% 14.66/6.75  tff(c_281, plain, (![A_38, B_37]: (k4_xboole_0(A_38, k2_xboole_0(B_37, A_38))=k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_262])).
% 14.66/6.75  tff(c_2265, plain, (![A_130, B_131, C_132]: (k4_xboole_0(k4_xboole_0(A_130, B_131), C_132)=k4_xboole_0(A_130, k2_xboole_0(B_131, C_132)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.66/6.75  tff(c_42, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.66/6.75  tff(c_7748, plain, (![C_253, A_254, B_255]: (k2_xboole_0(C_253, k4_xboole_0(A_254, k2_xboole_0(B_255, C_253)))=k2_xboole_0(C_253, k4_xboole_0(A_254, B_255)))), inference(superposition, [status(thm), theory('equality')], [c_2265, c_42])).
% 14.66/6.75  tff(c_7987, plain, (![A_38, B_37]: (k2_xboole_0(A_38, k4_xboole_0(A_38, B_37))=k2_xboole_0(A_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_281, c_7748])).
% 14.66/6.75  tff(c_8249, plain, (![A_256, B_257]: (k2_xboole_0(A_256, k4_xboole_0(A_256, B_257))=A_256)), inference(demodulation, [status(thm), theory('equality')], [c_7385, c_7987])).
% 14.66/6.75  tff(c_8527, plain, (![A_258, B_259]: (r1_tarski(k4_xboole_0(A_258, B_259), A_258))), inference(superposition, [status(thm), theory('equality')], [c_8249, c_85])).
% 14.66/6.75  tff(c_52, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.66/6.75  tff(c_1358, plain, (![A_104, C_105, B_106]: (r1_xboole_0(A_104, C_105) | ~r1_xboole_0(B_106, C_105) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.66/6.75  tff(c_1365, plain, (![A_107]: (r1_xboole_0(A_107, '#skF_6') | ~r1_tarski(A_107, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_1358])).
% 14.66/6.75  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.66/6.75  tff(c_1372, plain, (![A_107]: (k3_xboole_0(A_107, '#skF_6')=k1_xboole_0 | ~r1_tarski(A_107, '#skF_4'))), inference(resolution, [status(thm)], [c_1365, c_28])).
% 14.66/6.75  tff(c_8615, plain, (![B_259]: (k3_xboole_0(k4_xboole_0('#skF_4', B_259), '#skF_6')=k1_xboole_0)), inference(resolution, [status(thm)], [c_8527, c_1372])).
% 14.66/6.75  tff(c_54, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.66/6.75  tff(c_55, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_54])).
% 14.66/6.75  tff(c_284, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_262])).
% 14.66/6.75  tff(c_36715, plain, (![B_558, A_559, A_560]: (k2_xboole_0(B_558, k4_xboole_0(A_559, k2_xboole_0(B_558, A_560)))=k2_xboole_0(B_558, k4_xboole_0(A_559, A_560)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7748])).
% 14.66/6.75  tff(c_37336, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_284, c_36715])).
% 14.66/6.75  tff(c_37473, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7385, c_37336])).
% 14.66/6.75  tff(c_346, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.66/6.75  tff(c_365, plain, (![A_38, B_37]: (k3_xboole_0(A_38, k2_xboole_0(B_37, A_38))=A_38)), inference(resolution, [status(thm)], [c_85, c_346])).
% 14.66/6.75  tff(c_37726, plain, (k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_6')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_37473, c_365])).
% 14.66/6.75  tff(c_37821, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8615, c_37726])).
% 14.66/6.75  tff(c_37823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_37821])).
% 14.66/6.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.66/6.75  
% 14.66/6.75  Inference rules
% 14.66/6.75  ----------------------
% 14.66/6.75  #Ref     : 2
% 14.66/6.75  #Sup     : 9865
% 14.66/6.75  #Fact    : 0
% 14.66/6.75  #Define  : 0
% 14.66/6.75  #Split   : 6
% 14.66/6.75  #Chain   : 0
% 14.66/6.75  #Close   : 0
% 14.66/6.75  
% 14.66/6.75  Ordering : KBO
% 14.66/6.75  
% 14.66/6.75  Simplification rules
% 14.66/6.75  ----------------------
% 14.66/6.75  #Subsume      : 2633
% 14.66/6.75  #Demod        : 10068
% 14.66/6.75  #Tautology    : 4417
% 14.66/6.75  #SimpNegUnit  : 174
% 14.66/6.75  #BackRed      : 33
% 14.66/6.75  
% 14.66/6.75  #Partial instantiations: 0
% 14.66/6.75  #Strategies tried      : 1
% 14.66/6.75  
% 14.66/6.75  Timing (in seconds)
% 14.66/6.75  ----------------------
% 14.66/6.75  Preprocessing        : 0.31
% 14.80/6.75  Parsing              : 0.17
% 14.80/6.75  CNF conversion       : 0.02
% 14.80/6.75  Main loop            : 5.66
% 14.80/6.75  Inferencing          : 0.84
% 14.80/6.75  Reduction            : 3.21
% 14.80/6.75  Demodulation         : 2.81
% 14.80/6.75  BG Simplification    : 0.10
% 14.80/6.75  Subsumption          : 1.27
% 14.80/6.75  Abstraction          : 0.16
% 14.80/6.75  MUC search           : 0.00
% 14.80/6.75  Cooper               : 0.00
% 14.80/6.75  Total                : 6.00
% 14.80/6.75  Index Insertion      : 0.00
% 14.80/6.75  Index Deletion       : 0.00
% 14.80/6.75  Index Matching       : 0.00
% 14.80/6.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
