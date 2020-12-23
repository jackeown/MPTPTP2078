%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:36 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 102 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 142 expanded)
%              Number of equality atoms :   35 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_84,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_110,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_44,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_225,plain,(
    ! [D_75,B_76,A_77] :
      ( r2_hidden(D_75,B_76)
      | ~ r2_hidden(D_75,k3_xboole_0(A_77,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_236,plain,(
    ! [A_77,B_76] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_77,B_76)),B_76)
      | k3_xboole_0(A_77,B_76) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_225])).

tff(c_151,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(k1_tarski(A_55),B_56)
      | r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_274,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(k1_tarski(A_83),B_84) = k1_tarski(A_83)
      | r2_hidden(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_151,c_46])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1224,plain,(
    ! [D_140,B_141,A_142] :
      ( ~ r2_hidden(D_140,B_141)
      | ~ r2_hidden(D_140,k1_tarski(A_142))
      | r2_hidden(A_142,B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_24])).

tff(c_1684,plain,(
    ! [A_165,A_166] :
      ( ~ r2_hidden('#skF_5'(A_165),k1_tarski(A_166))
      | r2_hidden(A_166,A_165)
      | k1_xboole_0 = A_165 ) ),
    inference(resolution,[status(thm)],[c_40,c_1224])).

tff(c_17053,plain,(
    ! [A_5623,A_5624] :
      ( r2_hidden(A_5623,k3_xboole_0(A_5624,k1_tarski(A_5623)))
      | k3_xboole_0(A_5624,k1_tarski(A_5623)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_236,c_1684])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_17080,plain,(
    ! [A_5625,A_5626] :
      ( r2_hidden(A_5625,A_5626)
      | k3_xboole_0(A_5626,k1_tarski(A_5625)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_17053,c_8])).

tff(c_42,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_17128,plain,(
    ! [A_5626,A_5625] :
      ( k4_xboole_0(A_5626,k1_tarski(A_5625)) = k5_xboole_0(A_5626,k1_xboole_0)
      | r2_hidden(A_5625,A_5626) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17080,c_42])).

tff(c_17163,plain,(
    ! [A_5627,A_5628] :
      ( k4_xboole_0(A_5627,k1_tarski(A_5628)) = A_5627
      | r2_hidden(A_5628,A_5627) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_17128])).

tff(c_82,plain,
    ( k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8'
    | r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_178,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_17200,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_17163,c_178])).

tff(c_17224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_17200])).

tff(c_17225,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_74,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_156,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,(
    ! [B_59,A_60] : r2_hidden(B_59,k2_tarski(A_60,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_52])).

tff(c_177,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_174])).

tff(c_17226,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_86,plain,
    ( k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8'
    | k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_17238,plain,(
    k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17226,c_86])).

tff(c_17244,plain,(
    ! [D_5632,B_5633,A_5634] :
      ( ~ r2_hidden(D_5632,B_5633)
      | ~ r2_hidden(D_5632,k4_xboole_0(A_5634,B_5633)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_17256,plain,(
    ! [D_5635] :
      ( ~ r2_hidden(D_5635,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_5635,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17238,c_17244])).

tff(c_17260,plain,(
    ~ r2_hidden('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_177,c_17256])).

tff(c_17268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17225,c_17260])).

tff(c_17269,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_17317,plain,(
    ! [A_5645,B_5646] : k1_enumset1(A_5645,A_5645,B_5646) = k2_tarski(A_5645,B_5646) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17335,plain,(
    ! [B_5647,A_5648] : r2_hidden(B_5647,k2_tarski(A_5648,B_5647)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17317,c_52])).

tff(c_17338,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_17335])).

tff(c_17270,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_88,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_17371,plain,(
    k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17270,c_88])).

tff(c_17382,plain,(
    ! [D_5661] :
      ( ~ r2_hidden(D_5661,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_5661,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17371,c_24])).

tff(c_17386,plain,(
    ~ r2_hidden('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_17338,c_17382])).

tff(c_17394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17269,c_17386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.48/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/2.74  
% 7.48/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/2.75  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 7.48/2.75  
% 7.48/2.75  %Foreground sorts:
% 7.48/2.75  
% 7.48/2.75  
% 7.48/2.75  %Background operators:
% 7.48/2.75  
% 7.48/2.75  
% 7.48/2.75  %Foreground operators:
% 7.48/2.75  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.48/2.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.48/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.48/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.48/2.75  tff('#skF_11', type, '#skF_11': $i).
% 7.48/2.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.48/2.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.48/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.48/2.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.48/2.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.48/2.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.48/2.75  tff('#skF_10', type, '#skF_10': $i).
% 7.48/2.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.48/2.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.48/2.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.48/2.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.48/2.75  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 7.48/2.75  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.48/2.75  tff('#skF_9', type, '#skF_9': $i).
% 7.48/2.75  tff('#skF_8', type, '#skF_8': $i).
% 7.48/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.48/2.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.48/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.48/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.48/2.75  
% 7.65/2.76  tff(f_94, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.65/2.76  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.65/2.76  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.65/2.76  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.65/2.76  tff(f_88, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.65/2.76  tff(f_62, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.65/2.76  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.65/2.76  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.65/2.76  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.65/2.76  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.65/2.76  tff(f_77, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.65/2.76  tff(c_84, plain, (~r2_hidden('#skF_9', '#skF_8') | r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.76  tff(c_110, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 7.65/2.76  tff(c_44, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.65/2.76  tff(c_40, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.65/2.76  tff(c_225, plain, (![D_75, B_76, A_77]: (r2_hidden(D_75, B_76) | ~r2_hidden(D_75, k3_xboole_0(A_77, B_76)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.65/2.76  tff(c_236, plain, (![A_77, B_76]: (r2_hidden('#skF_5'(k3_xboole_0(A_77, B_76)), B_76) | k3_xboole_0(A_77, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_225])).
% 7.65/2.76  tff(c_151, plain, (![A_55, B_56]: (r1_xboole_0(k1_tarski(A_55), B_56) | r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.65/2.76  tff(c_46, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.65/2.76  tff(c_274, plain, (![A_83, B_84]: (k4_xboole_0(k1_tarski(A_83), B_84)=k1_tarski(A_83) | r2_hidden(A_83, B_84))), inference(resolution, [status(thm)], [c_151, c_46])).
% 7.65/2.76  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.65/2.76  tff(c_1224, plain, (![D_140, B_141, A_142]: (~r2_hidden(D_140, B_141) | ~r2_hidden(D_140, k1_tarski(A_142)) | r2_hidden(A_142, B_141))), inference(superposition, [status(thm), theory('equality')], [c_274, c_24])).
% 7.65/2.76  tff(c_1684, plain, (![A_165, A_166]: (~r2_hidden('#skF_5'(A_165), k1_tarski(A_166)) | r2_hidden(A_166, A_165) | k1_xboole_0=A_165)), inference(resolution, [status(thm)], [c_40, c_1224])).
% 7.65/2.76  tff(c_17053, plain, (![A_5623, A_5624]: (r2_hidden(A_5623, k3_xboole_0(A_5624, k1_tarski(A_5623))) | k3_xboole_0(A_5624, k1_tarski(A_5623))=k1_xboole_0)), inference(resolution, [status(thm)], [c_236, c_1684])).
% 7.65/2.76  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.65/2.76  tff(c_17080, plain, (![A_5625, A_5626]: (r2_hidden(A_5625, A_5626) | k3_xboole_0(A_5626, k1_tarski(A_5625))=k1_xboole_0)), inference(resolution, [status(thm)], [c_17053, c_8])).
% 7.65/2.76  tff(c_42, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.65/2.76  tff(c_17128, plain, (![A_5626, A_5625]: (k4_xboole_0(A_5626, k1_tarski(A_5625))=k5_xboole_0(A_5626, k1_xboole_0) | r2_hidden(A_5625, A_5626))), inference(superposition, [status(thm), theory('equality')], [c_17080, c_42])).
% 7.65/2.76  tff(c_17163, plain, (![A_5627, A_5628]: (k4_xboole_0(A_5627, k1_tarski(A_5628))=A_5627 | r2_hidden(A_5628, A_5627))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_17128])).
% 7.65/2.76  tff(c_82, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8' | r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.76  tff(c_178, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_82])).
% 7.65/2.76  tff(c_17200, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_17163, c_178])).
% 7.65/2.76  tff(c_17224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_17200])).
% 7.65/2.76  tff(c_17225, plain, (r2_hidden('#skF_11', '#skF_10')), inference(splitRight, [status(thm)], [c_82])).
% 7.65/2.76  tff(c_74, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.65/2.76  tff(c_156, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.65/2.76  tff(c_52, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.65/2.76  tff(c_174, plain, (![B_59, A_60]: (r2_hidden(B_59, k2_tarski(A_60, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_52])).
% 7.65/2.76  tff(c_177, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_174])).
% 7.65/2.76  tff(c_17226, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(splitRight, [status(thm)], [c_82])).
% 7.65/2.76  tff(c_86, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8' | k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.76  tff(c_17238, plain, (k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_17226, c_86])).
% 7.65/2.76  tff(c_17244, plain, (![D_5632, B_5633, A_5634]: (~r2_hidden(D_5632, B_5633) | ~r2_hidden(D_5632, k4_xboole_0(A_5634, B_5633)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.65/2.76  tff(c_17256, plain, (![D_5635]: (~r2_hidden(D_5635, k1_tarski('#skF_11')) | ~r2_hidden(D_5635, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_17238, c_17244])).
% 7.65/2.76  tff(c_17260, plain, (~r2_hidden('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_177, c_17256])).
% 7.65/2.76  tff(c_17268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17225, c_17260])).
% 7.65/2.76  tff(c_17269, plain, (r2_hidden('#skF_11', '#skF_10')), inference(splitRight, [status(thm)], [c_84])).
% 7.65/2.76  tff(c_17317, plain, (![A_5645, B_5646]: (k1_enumset1(A_5645, A_5645, B_5646)=k2_tarski(A_5645, B_5646))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.65/2.76  tff(c_17335, plain, (![B_5647, A_5648]: (r2_hidden(B_5647, k2_tarski(A_5648, B_5647)))), inference(superposition, [status(thm), theory('equality')], [c_17317, c_52])).
% 7.65/2.76  tff(c_17338, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_17335])).
% 7.65/2.76  tff(c_17270, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 7.65/2.76  tff(c_88, plain, (~r2_hidden('#skF_9', '#skF_8') | k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.76  tff(c_17371, plain, (k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_17270, c_88])).
% 7.65/2.76  tff(c_17382, plain, (![D_5661]: (~r2_hidden(D_5661, k1_tarski('#skF_11')) | ~r2_hidden(D_5661, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_17371, c_24])).
% 7.65/2.76  tff(c_17386, plain, (~r2_hidden('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_17338, c_17382])).
% 7.65/2.76  tff(c_17394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17269, c_17386])).
% 7.65/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.76  
% 7.65/2.76  Inference rules
% 7.65/2.76  ----------------------
% 7.65/2.76  #Ref     : 0
% 7.65/2.76  #Sup     : 3095
% 7.65/2.76  #Fact    : 2
% 7.65/2.76  #Define  : 0
% 7.65/2.76  #Split   : 2
% 7.65/2.76  #Chain   : 0
% 7.65/2.76  #Close   : 0
% 7.65/2.76  
% 7.65/2.76  Ordering : KBO
% 7.65/2.76  
% 7.65/2.76  Simplification rules
% 7.65/2.76  ----------------------
% 7.65/2.76  #Subsume      : 766
% 7.65/2.76  #Demod        : 602
% 7.65/2.76  #Tautology    : 215
% 7.65/2.76  #SimpNegUnit  : 41
% 7.65/2.76  #BackRed      : 0
% 7.65/2.76  
% 7.65/2.76  #Partial instantiations: 2736
% 7.65/2.76  #Strategies tried      : 1
% 7.65/2.76  
% 7.65/2.76  Timing (in seconds)
% 7.65/2.76  ----------------------
% 7.65/2.77  Preprocessing        : 0.33
% 7.65/2.77  Parsing              : 0.16
% 7.65/2.77  CNF conversion       : 0.03
% 7.65/2.77  Main loop            : 1.67
% 7.65/2.77  Inferencing          : 0.58
% 7.65/2.77  Reduction            : 0.54
% 7.65/2.77  Demodulation         : 0.36
% 7.65/2.77  BG Simplification    : 0.09
% 7.65/2.77  Subsumption          : 0.34
% 7.65/2.77  Abstraction          : 0.11
% 7.65/2.77  MUC search           : 0.00
% 7.65/2.77  Cooper               : 0.00
% 7.65/2.77  Total                : 2.04
% 7.65/2.77  Index Insertion      : 0.00
% 7.65/2.77  Index Deletion       : 0.00
% 7.65/2.77  Index Matching       : 0.00
% 7.65/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
