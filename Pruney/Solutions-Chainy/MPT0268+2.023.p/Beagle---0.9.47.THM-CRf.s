%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:37 EST 2020

% Result     : Theorem 4.91s
% Output     : CNFRefutation 4.91s
% Verified   : 
% Statistics : Number of formulae       :   80 (  97 expanded)
%              Number of leaves         :   35 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 117 expanded)
%              Number of equality atoms :   38 (  55 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_133,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_70,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(k1_tarski(A_36),B_37)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_138,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = A_57
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4681,plain,(
    ! [A_234,B_235] :
      ( k4_xboole_0(k1_tarski(A_234),B_235) = k1_tarski(A_234)
      | r2_hidden(A_234,B_235) ) ),
    inference(resolution,[status(thm)],[c_70,c_138])).

tff(c_34,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_317,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k4_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_156,plain,(
    ! [A_13,B_14] : k4_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_148])).

tff(c_816,plain,(
    ! [A_118,B_119] : k4_xboole_0(k3_xboole_0(A_118,B_119),A_118) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_156])).

tff(c_964,plain,(
    ! [C_125,B_126] : k3_xboole_0(C_125,k4_xboole_0(B_126,C_125)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_816])).

tff(c_26,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_987,plain,(
    ! [C_125,B_126] : k4_xboole_0(C_125,k4_xboole_0(B_126,C_125)) = k5_xboole_0(C_125,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_26])).

tff(c_1024,plain,(
    ! [C_125,B_126] : k4_xboole_0(C_125,k4_xboole_0(B_126,C_125)) = C_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_987])).

tff(c_4975,plain,(
    ! [B_238,A_239] :
      ( k4_xboole_0(B_238,k1_tarski(A_239)) = B_238
      | r2_hidden(A_239,B_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4681,c_1024])).

tff(c_72,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_135,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_5084,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4975,c_135])).

tff(c_5139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_5084])).

tff(c_5140,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_64,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5150,plain,(
    ! [A_242,B_243] : k1_enumset1(A_242,A_242,B_243) = k2_tarski(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [E_29,A_23,B_24] : r2_hidden(E_29,k1_enumset1(A_23,B_24,E_29)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5168,plain,(
    ! [B_244,A_245] : r2_hidden(B_244,k2_tarski(A_245,B_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5150,c_42])).

tff(c_5171,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_5168])).

tff(c_5141,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5181,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5141,c_76])).

tff(c_5516,plain,(
    ! [D_267,B_268,A_269] :
      ( ~ r2_hidden(D_267,B_268)
      | ~ r2_hidden(D_267,k4_xboole_0(A_269,B_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5550,plain,(
    ! [D_270] :
      ( ~ r2_hidden(D_270,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_270,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5181,c_5516])).

tff(c_5554,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_5171,c_5550])).

tff(c_5558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5140,c_5554])).

tff(c_5559,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5651,plain,(
    ! [A_284,B_285] : k1_enumset1(A_284,A_284,B_285) = k2_tarski(A_284,B_285) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5687,plain,(
    ! [B_286,A_287] : r2_hidden(B_286,k2_tarski(A_287,B_286)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5651,c_42])).

tff(c_5690,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_5687])).

tff(c_5560,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5601,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5560,c_78])).

tff(c_6039,plain,(
    ! [D_309,B_310,A_311] :
      ( ~ r2_hidden(D_309,B_310)
      | ~ r2_hidden(D_309,k4_xboole_0(A_311,B_310)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6109,plain,(
    ! [D_314] :
      ( ~ r2_hidden(D_314,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_314,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5601,c_6039])).

tff(c_6113,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_5690,c_6109])).

tff(c_6117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5559,c_6113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.91/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/2.00  
% 4.91/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/2.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 4.91/2.00  
% 4.91/2.00  %Foreground sorts:
% 4.91/2.00  
% 4.91/2.00  
% 4.91/2.00  %Background operators:
% 4.91/2.00  
% 4.91/2.00  
% 4.91/2.00  %Foreground operators:
% 4.91/2.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.91/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.91/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.91/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.91/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.91/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.91/2.00  tff('#skF_7', type, '#skF_7': $i).
% 4.91/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.91/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.91/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.91/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.91/2.00  tff('#skF_5', type, '#skF_5': $i).
% 4.91/2.00  tff('#skF_6', type, '#skF_6': $i).
% 4.91/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.91/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.91/2.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.91/2.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.91/2.00  tff('#skF_8', type, '#skF_8': $i).
% 4.91/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.91/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.91/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.91/2.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.91/2.00  
% 4.91/2.02  tff(f_87, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.91/2.02  tff(f_81, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.91/2.02  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.91/2.02  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.91/2.02  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.91/2.02  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.91/2.02  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.91/2.02  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.91/2.02  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.91/2.02  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.91/2.02  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.91/2.02  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.91/2.02  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.91/2.02  tff(c_74, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.91/2.02  tff(c_133, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 4.91/2.02  tff(c_70, plain, (![A_36, B_37]: (r1_xboole_0(k1_tarski(A_36), B_37) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.91/2.02  tff(c_138, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=A_57 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.91/2.02  tff(c_4681, plain, (![A_234, B_235]: (k4_xboole_0(k1_tarski(A_234), B_235)=k1_tarski(A_234) | r2_hidden(A_234, B_235))), inference(resolution, [status(thm)], [c_70, c_138])).
% 4.91/2.02  tff(c_34, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.91/2.02  tff(c_32, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.91/2.02  tff(c_317, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k4_xboole_0(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.91/2.02  tff(c_28, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.91/2.02  tff(c_148, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.91/2.02  tff(c_156, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_148])).
% 4.91/2.02  tff(c_816, plain, (![A_118, B_119]: (k4_xboole_0(k3_xboole_0(A_118, B_119), A_118)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_317, c_156])).
% 4.91/2.02  tff(c_964, plain, (![C_125, B_126]: (k3_xboole_0(C_125, k4_xboole_0(B_126, C_125))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_816])).
% 4.91/2.02  tff(c_26, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.91/2.02  tff(c_987, plain, (![C_125, B_126]: (k4_xboole_0(C_125, k4_xboole_0(B_126, C_125))=k5_xboole_0(C_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_964, c_26])).
% 4.91/2.02  tff(c_1024, plain, (![C_125, B_126]: (k4_xboole_0(C_125, k4_xboole_0(B_126, C_125))=C_125)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_987])).
% 4.91/2.02  tff(c_4975, plain, (![B_238, A_239]: (k4_xboole_0(B_238, k1_tarski(A_239))=B_238 | r2_hidden(A_239, B_238))), inference(superposition, [status(thm), theory('equality')], [c_4681, c_1024])).
% 4.91/2.02  tff(c_72, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.91/2.02  tff(c_135, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_72])).
% 4.91/2.02  tff(c_5084, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4975, c_135])).
% 4.91/2.02  tff(c_5139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_5084])).
% 4.91/2.02  tff(c_5140, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 4.91/2.02  tff(c_64, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.91/2.02  tff(c_5150, plain, (![A_242, B_243]: (k1_enumset1(A_242, A_242, B_243)=k2_tarski(A_242, B_243))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.91/2.02  tff(c_42, plain, (![E_29, A_23, B_24]: (r2_hidden(E_29, k1_enumset1(A_23, B_24, E_29)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.91/2.02  tff(c_5168, plain, (![B_244, A_245]: (r2_hidden(B_244, k2_tarski(A_245, B_244)))), inference(superposition, [status(thm), theory('equality')], [c_5150, c_42])).
% 4.91/2.02  tff(c_5171, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_5168])).
% 4.91/2.02  tff(c_5141, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_72])).
% 4.91/2.02  tff(c_76, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.91/2.02  tff(c_5181, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5141, c_76])).
% 4.91/2.02  tff(c_5516, plain, (![D_267, B_268, A_269]: (~r2_hidden(D_267, B_268) | ~r2_hidden(D_267, k4_xboole_0(A_269, B_268)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.91/2.02  tff(c_5550, plain, (![D_270]: (~r2_hidden(D_270, k1_tarski('#skF_8')) | ~r2_hidden(D_270, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5181, c_5516])).
% 4.91/2.02  tff(c_5554, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_5171, c_5550])).
% 4.91/2.02  tff(c_5558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5140, c_5554])).
% 4.91/2.02  tff(c_5559, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 4.91/2.02  tff(c_5651, plain, (![A_284, B_285]: (k1_enumset1(A_284, A_284, B_285)=k2_tarski(A_284, B_285))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.91/2.02  tff(c_5687, plain, (![B_286, A_287]: (r2_hidden(B_286, k2_tarski(A_287, B_286)))), inference(superposition, [status(thm), theory('equality')], [c_5651, c_42])).
% 4.91/2.02  tff(c_5690, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_5687])).
% 4.91/2.02  tff(c_5560, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 4.91/2.02  tff(c_78, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.91/2.02  tff(c_5601, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5560, c_78])).
% 4.91/2.02  tff(c_6039, plain, (![D_309, B_310, A_311]: (~r2_hidden(D_309, B_310) | ~r2_hidden(D_309, k4_xboole_0(A_311, B_310)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.91/2.02  tff(c_6109, plain, (![D_314]: (~r2_hidden(D_314, k1_tarski('#skF_8')) | ~r2_hidden(D_314, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5601, c_6039])).
% 4.91/2.02  tff(c_6113, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_5690, c_6109])).
% 4.91/2.02  tff(c_6117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5559, c_6113])).
% 4.91/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/2.02  
% 4.91/2.02  Inference rules
% 4.91/2.02  ----------------------
% 4.91/2.02  #Ref     : 0
% 4.91/2.02  #Sup     : 1538
% 4.91/2.02  #Fact    : 0
% 4.91/2.02  #Define  : 0
% 4.91/2.02  #Split   : 2
% 4.91/2.02  #Chain   : 0
% 4.91/2.02  #Close   : 0
% 4.91/2.02  
% 4.91/2.02  Ordering : KBO
% 4.91/2.02  
% 4.91/2.02  Simplification rules
% 4.91/2.02  ----------------------
% 4.91/2.02  #Subsume      : 84
% 4.91/2.02  #Demod        : 1096
% 4.91/2.02  #Tautology    : 1048
% 4.91/2.02  #SimpNegUnit  : 17
% 4.91/2.02  #BackRed      : 0
% 4.91/2.02  
% 4.91/2.02  #Partial instantiations: 0
% 4.91/2.02  #Strategies tried      : 1
% 4.91/2.02  
% 4.91/2.02  Timing (in seconds)
% 4.91/2.02  ----------------------
% 4.91/2.02  Preprocessing        : 0.36
% 4.91/2.02  Parsing              : 0.17
% 4.91/2.02  CNF conversion       : 0.03
% 4.91/2.02  Main loop            : 0.84
% 4.91/2.02  Inferencing          : 0.27
% 4.91/2.02  Reduction            : 0.35
% 4.91/2.02  Demodulation         : 0.28
% 4.91/2.02  BG Simplification    : 0.04
% 4.91/2.02  Subsumption          : 0.12
% 4.91/2.02  Abstraction          : 0.04
% 4.91/2.02  MUC search           : 0.00
% 4.91/2.02  Cooper               : 0.00
% 4.91/2.02  Total                : 1.22
% 4.91/2.02  Index Insertion      : 0.00
% 4.91/2.02  Index Deletion       : 0.00
% 4.91/2.02  Index Matching       : 0.00
% 4.91/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
