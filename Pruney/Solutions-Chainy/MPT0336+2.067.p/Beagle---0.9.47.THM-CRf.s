%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:09 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 144 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 210 expanded)
%              Number of equality atoms :   40 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_53,axiom,(
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

tff(f_79,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_22,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = A_49
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_148,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(resolution,[status(thm)],[c_22,c_124])).

tff(c_286,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_286])).

tff(c_719,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_740,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_719])).

tff(c_755,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_740])).

tff(c_50,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_313,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_286])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,k1_tarski(B_37)) = A_36
      | r2_hidden(B_37,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_360,plain,(
    ! [A_62,B_63] :
      ( r1_xboole_0(A_62,B_63)
      | k4_xboole_0(A_62,B_63) != A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1623,plain,(
    ! [A_155,B_156] :
      ( k3_xboole_0(A_155,B_156) = k1_xboole_0
      | k4_xboole_0(A_155,B_156) != A_155 ) ),
    inference(resolution,[status(thm)],[c_360,c_4])).

tff(c_1648,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,k1_tarski(B_37)) = k1_xboole_0
      | r2_hidden(B_37,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1623])).

tff(c_54,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_55,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_497,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_xboole_0(A_69,k4_xboole_0(C_70,B_71))
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4019,plain,(
    ! [A_214,C_215,B_216] :
      ( k4_xboole_0(A_214,k4_xboole_0(C_215,B_216)) = A_214
      | ~ r1_tarski(A_214,B_216) ) ),
    inference(resolution,[status(thm)],[c_497,c_32])).

tff(c_4955,plain,(
    ! [A_237,B_238] :
      ( k3_xboole_0(A_237,B_238) = A_237
      | ~ r1_tarski(A_237,B_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4019])).

tff(c_4959,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_4955])).

tff(c_2546,plain,(
    ! [A_187,B_188,C_189] : k3_xboole_0(k3_xboole_0(A_187,B_188),C_189) = k3_xboole_0(A_187,k3_xboole_0(B_188,C_189)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5769,plain,(
    ! [B_258,A_259,C_260] : k3_xboole_0(k3_xboole_0(B_258,A_259),C_260) = k3_xboole_0(A_259,k3_xboole_0(B_258,C_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2546])).

tff(c_5953,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',k1_tarski('#skF_5'))) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4959,c_5769])).

tff(c_6352,plain,
    ( k3_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_2')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1648,c_5953])).

tff(c_6361,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_6352])).

tff(c_6362,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6361])).

tff(c_52,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1530,plain,(
    ! [A_151,B_152,C_153] :
      ( ~ r1_xboole_0(A_151,B_152)
      | ~ r2_hidden(C_153,B_152)
      | ~ r2_hidden(C_153,A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5544,plain,(
    ! [C_250,B_251,A_252] :
      ( ~ r2_hidden(C_250,B_251)
      | ~ r2_hidden(C_250,A_252)
      | k3_xboole_0(A_252,B_251) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1530])).

tff(c_5556,plain,(
    ! [A_252] :
      ( ~ r2_hidden('#skF_5',A_252)
      | k3_xboole_0(A_252,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_5544])).

tff(c_6365,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6362,c_5556])).

tff(c_6379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_2,c_6365])).

tff(c_6380,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6361])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6431,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6380,c_16])).

tff(c_6450,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_6431])).

tff(c_30,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6603,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6450,c_30])).

tff(c_100,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | ~ r1_xboole_0(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_100])).

tff(c_3247,plain,(
    ! [A_199,C_200,B_201] :
      ( ~ r1_xboole_0(A_199,C_200)
      | ~ r1_xboole_0(A_199,B_201)
      | r1_xboole_0(A_199,k2_xboole_0(B_201,C_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10486,plain,(
    ! [B_314,C_315,A_316] :
      ( r1_xboole_0(k2_xboole_0(B_314,C_315),A_316)
      | ~ r1_xboole_0(A_316,C_315)
      | ~ r1_xboole_0(A_316,B_314) ) ),
    inference(resolution,[status(thm)],[c_3247,c_8])).

tff(c_48,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10507,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_10486,c_48])).

tff(c_10517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6603,c_108,c_10507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:04:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.18/2.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.69  
% 7.18/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.18/2.70  
% 7.18/2.70  %Foreground sorts:
% 7.18/2.70  
% 7.18/2.70  
% 7.18/2.70  %Background operators:
% 7.18/2.70  
% 7.18/2.70  
% 7.18/2.70  %Foreground operators:
% 7.18/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.18/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.18/2.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.18/2.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.18/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.18/2.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.18/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.18/2.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.18/2.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.18/2.70  tff('#skF_5', type, '#skF_5': $i).
% 7.18/2.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.18/2.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.18/2.70  tff('#skF_2', type, '#skF_2': $i).
% 7.18/2.70  tff('#skF_3', type, '#skF_3': $i).
% 7.18/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.18/2.70  tff('#skF_4', type, '#skF_4': $i).
% 7.18/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.18/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.18/2.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.18/2.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.18/2.70  
% 7.34/2.72  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.34/2.72  tff(f_83, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.34/2.72  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.34/2.72  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.34/2.72  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.34/2.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.34/2.72  tff(f_98, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.34/2.72  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.34/2.72  tff(f_87, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 7.34/2.72  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.34/2.72  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.34/2.72  tff(f_79, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.34/2.72  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.34/2.72  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.34/2.72  tff(c_22, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.34/2.72  tff(c_124, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=A_49 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.34/2.72  tff(c_148, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(resolution, [status(thm)], [c_22, c_124])).
% 7.34/2.72  tff(c_286, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.34/2.72  tff(c_314, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_286])).
% 7.34/2.72  tff(c_719, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.34/2.72  tff(c_740, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_314, c_719])).
% 7.34/2.72  tff(c_755, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_740])).
% 7.34/2.72  tff(c_50, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.34/2.72  tff(c_313, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_286])).
% 7.34/2.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.34/2.72  tff(c_46, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k1_tarski(B_37))=A_36 | r2_hidden(B_37, A_36))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.34/2.72  tff(c_360, plain, (![A_62, B_63]: (r1_xboole_0(A_62, B_63) | k4_xboole_0(A_62, B_63)!=A_62)), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.34/2.72  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.34/2.72  tff(c_1623, plain, (![A_155, B_156]: (k3_xboole_0(A_155, B_156)=k1_xboole_0 | k4_xboole_0(A_155, B_156)!=A_155)), inference(resolution, [status(thm)], [c_360, c_4])).
% 7.34/2.72  tff(c_1648, plain, (![A_36, B_37]: (k3_xboole_0(A_36, k1_tarski(B_37))=k1_xboole_0 | r2_hidden(B_37, A_36))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1623])).
% 7.34/2.72  tff(c_54, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.34/2.72  tff(c_55, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_54])).
% 7.34/2.72  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.34/2.72  tff(c_497, plain, (![A_69, C_70, B_71]: (r1_xboole_0(A_69, k4_xboole_0(C_70, B_71)) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.34/2.72  tff(c_32, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.34/2.72  tff(c_4019, plain, (![A_214, C_215, B_216]: (k4_xboole_0(A_214, k4_xboole_0(C_215, B_216))=A_214 | ~r1_tarski(A_214, B_216))), inference(resolution, [status(thm)], [c_497, c_32])).
% 7.34/2.72  tff(c_4955, plain, (![A_237, B_238]: (k3_xboole_0(A_237, B_238)=A_237 | ~r1_tarski(A_237, B_238))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4019])).
% 7.34/2.72  tff(c_4959, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_55, c_4955])).
% 7.34/2.72  tff(c_2546, plain, (![A_187, B_188, C_189]: (k3_xboole_0(k3_xboole_0(A_187, B_188), C_189)=k3_xboole_0(A_187, k3_xboole_0(B_188, C_189)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.34/2.72  tff(c_5769, plain, (![B_258, A_259, C_260]: (k3_xboole_0(k3_xboole_0(B_258, A_259), C_260)=k3_xboole_0(A_259, k3_xboole_0(B_258, C_260)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2546])).
% 7.34/2.72  tff(c_5953, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', k1_tarski('#skF_5')))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4959, c_5769])).
% 7.34/2.72  tff(c_6352, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_2') | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1648, c_5953])).
% 7.34/2.72  tff(c_6361, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_6352])).
% 7.34/2.72  tff(c_6362, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_6361])).
% 7.34/2.72  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.34/2.72  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.34/2.72  tff(c_1530, plain, (![A_151, B_152, C_153]: (~r1_xboole_0(A_151, B_152) | ~r2_hidden(C_153, B_152) | ~r2_hidden(C_153, A_151))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.34/2.72  tff(c_5544, plain, (![C_250, B_251, A_252]: (~r2_hidden(C_250, B_251) | ~r2_hidden(C_250, A_252) | k3_xboole_0(A_252, B_251)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1530])).
% 7.34/2.72  tff(c_5556, plain, (![A_252]: (~r2_hidden('#skF_5', A_252) | k3_xboole_0(A_252, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_5544])).
% 7.34/2.72  tff(c_6365, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6362, c_5556])).
% 7.34/2.72  tff(c_6379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_2, c_6365])).
% 7.34/2.72  tff(c_6380, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6361])).
% 7.34/2.72  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.34/2.72  tff(c_6431, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6380, c_16])).
% 7.34/2.72  tff(c_6450, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_755, c_6431])).
% 7.34/2.72  tff(c_30, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.34/2.72  tff(c_6603, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6450, c_30])).
% 7.34/2.72  tff(c_100, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | ~r1_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.34/2.72  tff(c_108, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_100])).
% 7.34/2.72  tff(c_3247, plain, (![A_199, C_200, B_201]: (~r1_xboole_0(A_199, C_200) | ~r1_xboole_0(A_199, B_201) | r1_xboole_0(A_199, k2_xboole_0(B_201, C_200)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.34/2.72  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.34/2.72  tff(c_10486, plain, (![B_314, C_315, A_316]: (r1_xboole_0(k2_xboole_0(B_314, C_315), A_316) | ~r1_xboole_0(A_316, C_315) | ~r1_xboole_0(A_316, B_314))), inference(resolution, [status(thm)], [c_3247, c_8])).
% 7.34/2.72  tff(c_48, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.34/2.72  tff(c_10507, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_10486, c_48])).
% 7.34/2.72  tff(c_10517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6603, c_108, c_10507])).
% 7.34/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/2.72  
% 7.34/2.72  Inference rules
% 7.34/2.72  ----------------------
% 7.34/2.72  #Ref     : 0
% 7.34/2.72  #Sup     : 2619
% 7.34/2.72  #Fact    : 0
% 7.34/2.72  #Define  : 0
% 7.34/2.72  #Split   : 4
% 7.34/2.72  #Chain   : 0
% 7.34/2.72  #Close   : 0
% 7.34/2.72  
% 7.34/2.72  Ordering : KBO
% 7.34/2.72  
% 7.34/2.72  Simplification rules
% 7.34/2.72  ----------------------
% 7.34/2.72  #Subsume      : 84
% 7.34/2.72  #Demod        : 2122
% 7.34/2.72  #Tautology    : 1663
% 7.34/2.72  #SimpNegUnit  : 8
% 7.34/2.72  #BackRed      : 4
% 7.34/2.72  
% 7.34/2.72  #Partial instantiations: 0
% 7.34/2.72  #Strategies tried      : 1
% 7.34/2.72  
% 7.34/2.72  Timing (in seconds)
% 7.34/2.72  ----------------------
% 7.34/2.73  Preprocessing        : 0.33
% 7.34/2.73  Parsing              : 0.18
% 7.34/2.73  CNF conversion       : 0.02
% 7.34/2.73  Main loop            : 1.54
% 7.34/2.73  Inferencing          : 0.42
% 7.34/2.73  Reduction            : 0.71
% 7.34/2.73  Demodulation         : 0.57
% 7.34/2.73  BG Simplification    : 0.04
% 7.34/2.73  Subsumption          : 0.27
% 7.34/2.73  Abstraction          : 0.06
% 7.34/2.73  MUC search           : 0.00
% 7.34/2.73  Cooper               : 0.00
% 7.34/2.73  Total                : 1.92
% 7.34/2.73  Index Insertion      : 0.00
% 7.34/2.73  Index Deletion       : 0.00
% 7.34/2.73  Index Matching       : 0.00
% 7.34/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
