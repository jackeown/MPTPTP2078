%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:10 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 130 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 183 expanded)
%              Number of equality atoms :   44 (  71 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
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

tff(c_370,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_388,plain,(
    ! [A_69,B_70] : r1_tarski(k3_xboole_0(A_69,B_70),A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_16])).

tff(c_48,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_99,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = A_43
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_110,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_99])).

tff(c_1005,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_xboole_0(A_105,k4_xboole_0(C_106,B_107))
      | ~ r1_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1060,plain,(
    ! [A_110] :
      ( r1_xboole_0(A_110,'#skF_4')
      | ~ r1_tarski(A_110,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1005])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1737,plain,(
    ! [A_134] :
      ( k4_xboole_0(A_134,'#skF_4') = A_134
      | ~ r1_tarski(A_134,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1060,c_30])).

tff(c_1759,plain,(
    ! [B_70] : k4_xboole_0(k3_xboole_0('#skF_3',B_70),'#skF_4') = k3_xboole_0('#skF_3',B_70) ),
    inference(resolution,[status(thm)],[c_388,c_1737])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_111,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_141,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_xboole_0(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_141])).

tff(c_891,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_915,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = k4_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_891])).

tff(c_929,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_915])).

tff(c_28,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_229,plain,(
    ! [A_53,B_54] : k3_xboole_0(k4_xboole_0(A_53,B_54),B_54) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_141])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_266,plain,(
    ! [B_55,A_56] : k3_xboole_0(B_55,k4_xboole_0(A_56,B_55)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_2])).

tff(c_282,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_266])).

tff(c_903,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_891])).

tff(c_963,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_903])).

tff(c_982,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_963,c_28])).

tff(c_1639,plain,(
    ! [A_129,C_130,B_131] :
      ( ~ r1_xboole_0(A_129,C_130)
      | ~ r1_xboole_0(A_129,B_131)
      | r1_xboole_0(A_129,k2_xboole_0(B_131,C_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12978,plain,(
    ! [A_329,B_330,C_331] :
      ( k3_xboole_0(A_329,k2_xboole_0(B_330,C_331)) = k1_xboole_0
      | ~ r1_xboole_0(A_329,C_331)
      | ~ r1_xboole_0(A_329,B_330) ) ),
    inference(resolution,[status(thm)],[c_1639,c_4])).

tff(c_154,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(A_49,B_50)
      | k3_xboole_0(A_49,B_50) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_163,plain,(
    k3_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_46])).

tff(c_167,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_13138,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12978,c_167])).

tff(c_13239,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_13138])).

tff(c_13273,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_13239])).

tff(c_335,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,k1_tarski(B_66)) = A_65
      | r2_hidden(B_66,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_361,plain,(
    ! [A_67,B_68] :
      ( r1_xboole_0(A_67,k1_tarski(B_68))
      | r2_hidden(B_68,A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_28])).

tff(c_5996,plain,(
    ! [A_218,B_219] :
      ( k3_xboole_0(A_218,k1_tarski(B_219)) = k1_xboole_0
      | r2_hidden(B_219,A_218) ) ),
    inference(resolution,[status(thm)],[c_361,c_4])).

tff(c_13635,plain,(
    ! [B_335,A_336] :
      ( k3_xboole_0(k1_tarski(B_335),A_336) = k1_xboole_0
      | r2_hidden(B_335,A_336) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5996])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_7530,plain,(
    ! [A_250,C_251,B_252] :
      ( k4_xboole_0(A_250,k4_xboole_0(C_251,B_252)) = A_250
      | ~ r1_tarski(A_250,B_252) ) ),
    inference(resolution,[status(thm)],[c_1005,c_30])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_11800,plain,(
    ! [C_301,B_302] :
      ( k3_xboole_0(C_301,B_302) = C_301
      | ~ r1_tarski(C_301,B_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7530,c_18])).

tff(c_11837,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_11800])).

tff(c_12026,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11837,c_2])).

tff(c_13641,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13635,c_12026])).

tff(c_13867,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_13273,c_13641])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1410,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,B_118)
      | ~ r2_hidden(C_119,A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10805,plain,(
    ! [C_290,B_291,A_292] :
      ( ~ r2_hidden(C_290,B_291)
      | ~ r2_hidden(C_290,A_292)
      | k4_xboole_0(A_292,B_291) != A_292 ) ),
    inference(resolution,[status(thm)],[c_32,c_1410])).

tff(c_10817,plain,(
    ! [A_292] :
      ( ~ r2_hidden('#skF_5',A_292)
      | k4_xboole_0(A_292,'#skF_4') != A_292 ) ),
    inference(resolution,[status(thm)],[c_50,c_10805])).

tff(c_13921,plain,(
    k4_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') != k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_13867,c_10817])).

tff(c_13956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_13921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:32:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.55/2.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/2.70  
% 7.55/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/2.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.55/2.70  
% 7.55/2.70  %Foreground sorts:
% 7.55/2.70  
% 7.55/2.70  
% 7.55/2.70  %Background operators:
% 7.55/2.70  
% 7.55/2.70  
% 7.55/2.70  %Foreground operators:
% 7.55/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.55/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.55/2.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.55/2.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.55/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.55/2.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.55/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.55/2.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.55/2.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.55/2.70  tff('#skF_5', type, '#skF_5': $i).
% 7.55/2.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.55/2.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.55/2.70  tff('#skF_2', type, '#skF_2': $i).
% 7.55/2.70  tff('#skF_3', type, '#skF_3': $i).
% 7.55/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.55/2.70  tff('#skF_4', type, '#skF_4': $i).
% 7.55/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.55/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.55/2.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.55/2.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.55/2.70  
% 7.65/2.72  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.65/2.72  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.65/2.72  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.65/2.72  tff(f_79, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.65/2.72  tff(f_83, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 7.65/2.72  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.65/2.72  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.65/2.72  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.65/2.72  tff(f_75, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.65/2.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.65/2.72  tff(f_73, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.65/2.72  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.65/2.72  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.65/2.72  tff(c_370, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.65/2.72  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.65/2.72  tff(c_388, plain, (![A_69, B_70]: (r1_tarski(k3_xboole_0(A_69, B_70), A_69))), inference(superposition, [status(thm), theory('equality')], [c_370, c_16])).
% 7.65/2.72  tff(c_48, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.65/2.72  tff(c_99, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=A_43 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.65/2.72  tff(c_110, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_99])).
% 7.65/2.72  tff(c_1005, plain, (![A_105, C_106, B_107]: (r1_xboole_0(A_105, k4_xboole_0(C_106, B_107)) | ~r1_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.65/2.72  tff(c_1060, plain, (![A_110]: (r1_xboole_0(A_110, '#skF_4') | ~r1_tarski(A_110, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_1005])).
% 7.65/2.72  tff(c_30, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.65/2.72  tff(c_1737, plain, (![A_134]: (k4_xboole_0(A_134, '#skF_4')=A_134 | ~r1_tarski(A_134, '#skF_3'))), inference(resolution, [status(thm)], [c_1060, c_30])).
% 7.65/2.72  tff(c_1759, plain, (![B_70]: (k4_xboole_0(k3_xboole_0('#skF_3', B_70), '#skF_4')=k3_xboole_0('#skF_3', B_70))), inference(resolution, [status(thm)], [c_388, c_1737])).
% 7.65/2.72  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.72  tff(c_20, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.65/2.72  tff(c_111, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(resolution, [status(thm)], [c_20, c_99])).
% 7.65/2.72  tff(c_141, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.72  tff(c_153, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_141])).
% 7.65/2.72  tff(c_891, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.65/2.72  tff(c_915, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=k4_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_153, c_891])).
% 7.65/2.72  tff(c_929, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_915])).
% 7.65/2.72  tff(c_28, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.65/2.72  tff(c_229, plain, (![A_53, B_54]: (k3_xboole_0(k4_xboole_0(A_53, B_54), B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_141])).
% 7.65/2.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.65/2.72  tff(c_266, plain, (![B_55, A_56]: (k3_xboole_0(B_55, k4_xboole_0(A_56, B_55))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_2])).
% 7.65/2.72  tff(c_282, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_110, c_266])).
% 7.65/2.72  tff(c_903, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_282, c_891])).
% 7.65/2.72  tff(c_963, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_929, c_903])).
% 7.65/2.72  tff(c_982, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_963, c_28])).
% 7.65/2.72  tff(c_1639, plain, (![A_129, C_130, B_131]: (~r1_xboole_0(A_129, C_130) | ~r1_xboole_0(A_129, B_131) | r1_xboole_0(A_129, k2_xboole_0(B_131, C_130)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.65/2.72  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.72  tff(c_12978, plain, (![A_329, B_330, C_331]: (k3_xboole_0(A_329, k2_xboole_0(B_330, C_331))=k1_xboole_0 | ~r1_xboole_0(A_329, C_331) | ~r1_xboole_0(A_329, B_330))), inference(resolution, [status(thm)], [c_1639, c_4])).
% 7.65/2.72  tff(c_154, plain, (![A_49, B_50]: (r1_xboole_0(A_49, B_50) | k3_xboole_0(A_49, B_50)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.65/2.72  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.65/2.72  tff(c_163, plain, (k3_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_46])).
% 7.65/2.72  tff(c_167, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_163])).
% 7.65/2.72  tff(c_13138, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12978, c_167])).
% 7.65/2.72  tff(c_13239, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_982, c_13138])).
% 7.65/2.72  tff(c_13273, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_13239])).
% 7.65/2.72  tff(c_335, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k1_tarski(B_66))=A_65 | r2_hidden(B_66, A_65))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.72  tff(c_361, plain, (![A_67, B_68]: (r1_xboole_0(A_67, k1_tarski(B_68)) | r2_hidden(B_68, A_67))), inference(superposition, [status(thm), theory('equality')], [c_335, c_28])).
% 7.65/2.72  tff(c_5996, plain, (![A_218, B_219]: (k3_xboole_0(A_218, k1_tarski(B_219))=k1_xboole_0 | r2_hidden(B_219, A_218))), inference(resolution, [status(thm)], [c_361, c_4])).
% 7.65/2.72  tff(c_13635, plain, (![B_335, A_336]: (k3_xboole_0(k1_tarski(B_335), A_336)=k1_xboole_0 | r2_hidden(B_335, A_336))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5996])).
% 7.65/2.72  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.65/2.72  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 7.65/2.72  tff(c_7530, plain, (![A_250, C_251, B_252]: (k4_xboole_0(A_250, k4_xboole_0(C_251, B_252))=A_250 | ~r1_tarski(A_250, B_252))), inference(resolution, [status(thm)], [c_1005, c_30])).
% 7.65/2.72  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.65/2.72  tff(c_11800, plain, (![C_301, B_302]: (k3_xboole_0(C_301, B_302)=C_301 | ~r1_tarski(C_301, B_302))), inference(superposition, [status(thm), theory('equality')], [c_7530, c_18])).
% 7.65/2.72  tff(c_11837, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_11800])).
% 7.65/2.72  tff(c_12026, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11837, c_2])).
% 7.65/2.72  tff(c_13641, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13635, c_12026])).
% 7.65/2.72  tff(c_13867, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_13273, c_13641])).
% 7.65/2.72  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.65/2.72  tff(c_32, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.65/2.72  tff(c_1410, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, B_118) | ~r2_hidden(C_119, A_117))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.65/2.72  tff(c_10805, plain, (![C_290, B_291, A_292]: (~r2_hidden(C_290, B_291) | ~r2_hidden(C_290, A_292) | k4_xboole_0(A_292, B_291)!=A_292)), inference(resolution, [status(thm)], [c_32, c_1410])).
% 7.65/2.72  tff(c_10817, plain, (![A_292]: (~r2_hidden('#skF_5', A_292) | k4_xboole_0(A_292, '#skF_4')!=A_292)), inference(resolution, [status(thm)], [c_50, c_10805])).
% 7.65/2.72  tff(c_13921, plain, (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')!=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_13867, c_10817])).
% 7.65/2.72  tff(c_13956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1759, c_13921])).
% 7.65/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.72  
% 7.65/2.72  Inference rules
% 7.65/2.72  ----------------------
% 7.65/2.72  #Ref     : 1
% 7.65/2.72  #Sup     : 3436
% 7.65/2.72  #Fact    : 0
% 7.65/2.72  #Define  : 0
% 7.65/2.72  #Split   : 2
% 7.65/2.72  #Chain   : 0
% 7.65/2.72  #Close   : 0
% 7.65/2.72  
% 7.65/2.72  Ordering : KBO
% 7.65/2.72  
% 7.65/2.72  Simplification rules
% 7.65/2.72  ----------------------
% 7.65/2.72  #Subsume      : 626
% 7.65/2.72  #Demod        : 2356
% 7.65/2.72  #Tautology    : 2160
% 7.65/2.72  #SimpNegUnit  : 62
% 7.65/2.72  #BackRed      : 0
% 7.65/2.72  
% 7.65/2.72  #Partial instantiations: 0
% 7.65/2.72  #Strategies tried      : 1
% 7.65/2.72  
% 7.65/2.72  Timing (in seconds)
% 7.65/2.72  ----------------------
% 7.65/2.72  Preprocessing        : 0.33
% 7.65/2.72  Parsing              : 0.18
% 7.65/2.72  CNF conversion       : 0.02
% 7.65/2.72  Main loop            : 1.63
% 7.65/2.72  Inferencing          : 0.42
% 7.65/2.72  Reduction            : 0.78
% 7.65/2.72  Demodulation         : 0.63
% 7.65/2.72  BG Simplification    : 0.04
% 7.65/2.72  Subsumption          : 0.29
% 7.65/2.72  Abstraction          : 0.06
% 7.65/2.72  MUC search           : 0.00
% 7.65/2.72  Cooper               : 0.00
% 7.65/2.72  Total                : 1.99
% 7.65/2.72  Index Insertion      : 0.00
% 7.65/2.72  Index Deletion       : 0.00
% 7.65/2.72  Index Matching       : 0.00
% 7.65/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
