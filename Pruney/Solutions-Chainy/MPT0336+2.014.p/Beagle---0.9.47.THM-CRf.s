%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:02 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 136 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 216 expanded)
%              Number of equality atoms :   24 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_48,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_146,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_162,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_146])).

tff(c_476,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_499,plain,(
    ! [C_81] :
      ( ~ r1_xboole_0('#skF_5','#skF_4')
      | ~ r2_hidden(C_81,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_476])).

tff(c_516,plain,(
    ! [C_81] : ~ r2_hidden(C_81,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_499])).

tff(c_50,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_949,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ r1_xboole_0(A_108,B_109)
      | ~ r2_hidden(C_110,B_109)
      | ~ r2_hidden(C_110,A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_980,plain,(
    ! [C_111] :
      ( ~ r2_hidden(C_111,'#skF_4')
      | ~ r2_hidden(C_111,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_949])).

tff(c_994,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_980])).

tff(c_254,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(A_55,B_56)
      | k3_xboole_0(A_55,B_56) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_264,plain,(
    ! [B_56,A_55] :
      ( r1_xboole_0(B_56,A_55)
      | k3_xboole_0(A_55,B_56) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_254,c_10])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_52])).

tff(c_275,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_279,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_275])).

tff(c_267,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(k1_tarski(A_57),B_58)
      | r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_681,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(k1_tarski(A_94),B_95) = k1_xboole_0
      | r2_hidden(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_267,c_6])).

tff(c_843,plain,(
    ! [A_104,A_105] :
      ( k3_xboole_0(A_104,k1_tarski(A_105)) = k1_xboole_0
      | r2_hidden(A_105,A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_681])).

tff(c_891,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_843])).

tff(c_1170,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_891])).

tff(c_508,plain,(
    ! [B_4,A_3,C_81] :
      ( ~ r1_xboole_0(B_4,A_3)
      | ~ r2_hidden(C_81,k3_xboole_0(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_476])).

tff(c_1177,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1170,c_508])).

tff(c_1185,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_264,c_1177])).

tff(c_28,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_161,plain,(
    ! [A_26] : k3_xboole_0(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_146])).

tff(c_727,plain,(
    ! [A_3,A_94] :
      ( k3_xboole_0(A_3,k1_tarski(A_94)) = k1_xboole_0
      | r2_hidden(A_94,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_681])).

tff(c_1197,plain,(
    ! [A_122,B_123,C_124] : k3_xboole_0(k3_xboole_0(A_122,B_123),C_124) = k3_xboole_0(A_122,k3_xboole_0(B_123,C_124)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5038,plain,(
    ! [A_197,B_198,C_199] : k3_xboole_0(k3_xboole_0(A_197,B_198),C_199) = k3_xboole_0(B_198,k3_xboole_0(A_197,C_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1197])).

tff(c_5235,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',k1_tarski('#skF_6'))) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5038,c_279])).

tff(c_5645,plain,
    ( k3_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_5235])).

tff(c_5659,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_5645])).

tff(c_5661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_994,c_1185,c_5659])).

tff(c_5662,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_891])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_2'(A_14,B_15),k3_xboole_0(A_14,B_15))
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5672,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5662,c_18])).

tff(c_5701,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_5672])).

tff(c_64,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | ~ r1_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_6142,plain,(
    ! [A_212,C_213,B_214] :
      ( ~ r1_xboole_0(A_212,C_213)
      | ~ r1_xboole_0(A_212,B_214)
      | r1_xboole_0(A_212,k2_xboole_0(B_214,C_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12095,plain,(
    ! [B_314,C_315,A_316] :
      ( r1_xboole_0(k2_xboole_0(B_314,C_315),A_316)
      | ~ r1_xboole_0(A_316,C_315)
      | ~ r1_xboole_0(A_316,B_314) ) ),
    inference(resolution,[status(thm)],[c_6142,c_10])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12113,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12095,c_46])).

tff(c_12128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5701,c_70,c_12113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:40:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.03/2.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.81  
% 8.03/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.03/2.81  
% 8.03/2.81  %Foreground sorts:
% 8.03/2.81  
% 8.03/2.81  
% 8.03/2.81  %Background operators:
% 8.03/2.81  
% 8.03/2.81  
% 8.03/2.81  %Foreground operators:
% 8.03/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.03/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.03/2.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.03/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.03/2.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.03/2.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.03/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.03/2.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.03/2.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.03/2.81  tff('#skF_5', type, '#skF_5': $i).
% 8.03/2.81  tff('#skF_6', type, '#skF_6': $i).
% 8.03/2.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.03/2.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.03/2.81  tff('#skF_3', type, '#skF_3': $i).
% 8.03/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.03/2.81  tff('#skF_4', type, '#skF_4': $i).
% 8.03/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.03/2.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.03/2.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.03/2.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.03/2.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.03/2.81  
% 8.03/2.83  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.03/2.83  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.03/2.83  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.03/2.83  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.03/2.83  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.03/2.83  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.03/2.83  tff(f_77, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.03/2.83  tff(f_108, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.03/2.83  tff(f_79, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.03/2.83  tff(f_73, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 8.03/2.83  tff(f_95, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.03/2.83  tff(c_48, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.03/2.83  tff(c_146, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.03/2.83  tff(c_162, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_146])).
% 8.03/2.83  tff(c_476, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.03/2.83  tff(c_499, plain, (![C_81]: (~r1_xboole_0('#skF_5', '#skF_4') | ~r2_hidden(C_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_162, c_476])).
% 8.03/2.83  tff(c_516, plain, (![C_81]: (~r2_hidden(C_81, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_499])).
% 8.03/2.83  tff(c_50, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.03/2.83  tff(c_949, plain, (![A_108, B_109, C_110]: (~r1_xboole_0(A_108, B_109) | ~r2_hidden(C_110, B_109) | ~r2_hidden(C_110, A_108))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.03/2.83  tff(c_980, plain, (![C_111]: (~r2_hidden(C_111, '#skF_4') | ~r2_hidden(C_111, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_949])).
% 8.03/2.83  tff(c_994, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_980])).
% 8.03/2.83  tff(c_254, plain, (![A_55, B_56]: (r1_xboole_0(A_55, B_56) | k3_xboole_0(A_55, B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.03/2.83  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.03/2.83  tff(c_264, plain, (![B_56, A_55]: (r1_xboole_0(B_56, A_55) | k3_xboole_0(A_55, B_56)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_254, c_10])).
% 8.03/2.83  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.03/2.83  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.03/2.83  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_52])).
% 8.03/2.83  tff(c_275, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.03/2.83  tff(c_279, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_53, c_275])).
% 8.03/2.83  tff(c_267, plain, (![A_57, B_58]: (r1_xboole_0(k1_tarski(A_57), B_58) | r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.03/2.83  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.03/2.83  tff(c_681, plain, (![A_94, B_95]: (k3_xboole_0(k1_tarski(A_94), B_95)=k1_xboole_0 | r2_hidden(A_94, B_95))), inference(resolution, [status(thm)], [c_267, c_6])).
% 8.03/2.83  tff(c_843, plain, (![A_104, A_105]: (k3_xboole_0(A_104, k1_tarski(A_105))=k1_xboole_0 | r2_hidden(A_105, A_104))), inference(superposition, [status(thm), theory('equality')], [c_4, c_681])).
% 8.03/2.83  tff(c_891, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_279, c_843])).
% 8.03/2.83  tff(c_1170, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_891])).
% 8.03/2.83  tff(c_508, plain, (![B_4, A_3, C_81]: (~r1_xboole_0(B_4, A_3) | ~r2_hidden(C_81, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_476])).
% 8.03/2.83  tff(c_1177, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1170, c_508])).
% 8.03/2.83  tff(c_1185, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_264, c_1177])).
% 8.03/2.83  tff(c_28, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.03/2.83  tff(c_161, plain, (![A_26]: (k3_xboole_0(A_26, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_146])).
% 8.03/2.83  tff(c_727, plain, (![A_3, A_94]: (k3_xboole_0(A_3, k1_tarski(A_94))=k1_xboole_0 | r2_hidden(A_94, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_681])).
% 8.03/2.83  tff(c_1197, plain, (![A_122, B_123, C_124]: (k3_xboole_0(k3_xboole_0(A_122, B_123), C_124)=k3_xboole_0(A_122, k3_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.03/2.83  tff(c_5038, plain, (![A_197, B_198, C_199]: (k3_xboole_0(k3_xboole_0(A_197, B_198), C_199)=k3_xboole_0(B_198, k3_xboole_0(A_197, C_199)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1197])).
% 8.03/2.83  tff(c_5235, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', k1_tarski('#skF_6')))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5038, c_279])).
% 8.03/2.83  tff(c_5645, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_727, c_5235])).
% 8.03/2.83  tff(c_5659, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_5645])).
% 8.03/2.83  tff(c_5661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_994, c_1185, c_5659])).
% 8.03/2.83  tff(c_5662, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_891])).
% 8.03/2.83  tff(c_18, plain, (![A_14, B_15]: (r2_hidden('#skF_2'(A_14, B_15), k3_xboole_0(A_14, B_15)) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.03/2.83  tff(c_5672, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5662, c_18])).
% 8.03/2.83  tff(c_5701, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_516, c_5672])).
% 8.03/2.83  tff(c_64, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | ~r1_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.03/2.83  tff(c_70, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_64])).
% 8.03/2.83  tff(c_6142, plain, (![A_212, C_213, B_214]: (~r1_xboole_0(A_212, C_213) | ~r1_xboole_0(A_212, B_214) | r1_xboole_0(A_212, k2_xboole_0(B_214, C_213)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.03/2.83  tff(c_12095, plain, (![B_314, C_315, A_316]: (r1_xboole_0(k2_xboole_0(B_314, C_315), A_316) | ~r1_xboole_0(A_316, C_315) | ~r1_xboole_0(A_316, B_314))), inference(resolution, [status(thm)], [c_6142, c_10])).
% 8.03/2.83  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.03/2.83  tff(c_12113, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_12095, c_46])).
% 8.03/2.83  tff(c_12128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5701, c_70, c_12113])).
% 8.03/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.83  
% 8.03/2.83  Inference rules
% 8.03/2.83  ----------------------
% 8.03/2.83  #Ref     : 0
% 8.03/2.83  #Sup     : 3043
% 8.03/2.83  #Fact    : 0
% 8.03/2.83  #Define  : 0
% 8.03/2.83  #Split   : 3
% 8.03/2.83  #Chain   : 0
% 8.03/2.83  #Close   : 0
% 8.03/2.83  
% 8.03/2.83  Ordering : KBO
% 8.03/2.83  
% 8.03/2.83  Simplification rules
% 8.03/2.83  ----------------------
% 8.03/2.83  #Subsume      : 197
% 8.03/2.83  #Demod        : 2615
% 8.03/2.83  #Tautology    : 1882
% 8.03/2.83  #SimpNegUnit  : 94
% 8.03/2.83  #BackRed      : 5
% 8.03/2.83  
% 8.03/2.83  #Partial instantiations: 0
% 8.03/2.83  #Strategies tried      : 1
% 8.03/2.83  
% 8.03/2.83  Timing (in seconds)
% 8.03/2.83  ----------------------
% 8.03/2.83  Preprocessing        : 0.34
% 8.03/2.83  Parsing              : 0.19
% 8.03/2.83  CNF conversion       : 0.02
% 8.03/2.83  Main loop            : 1.72
% 8.03/2.83  Inferencing          : 0.45
% 8.03/2.83  Reduction            : 0.84
% 8.03/2.83  Demodulation         : 0.70
% 8.03/2.83  BG Simplification    : 0.05
% 8.03/2.83  Subsumption          : 0.27
% 8.03/2.83  Abstraction          : 0.06
% 8.03/2.83  MUC search           : 0.00
% 8.03/2.83  Cooper               : 0.00
% 8.03/2.83  Total                : 2.09
% 8.03/2.83  Index Insertion      : 0.00
% 8.03/2.83  Index Deletion       : 0.00
% 8.03/2.83  Index Matching       : 0.00
% 8.03/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
