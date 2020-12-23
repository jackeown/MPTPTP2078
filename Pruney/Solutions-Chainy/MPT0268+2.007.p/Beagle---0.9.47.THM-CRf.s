%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:34 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 112 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 141 expanded)
%              Number of equality atoms :   44 (  70 expanded)
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

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_80,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_78,axiom,(
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

tff(c_80,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_105,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_36,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [B_10] : k4_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_145])).

tff(c_228,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_246,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_228])).

tff(c_250,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_246])).

tff(c_328,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_340,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_328])).

tff(c_352,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_340])).

tff(c_76,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),B_39)
      | r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_167,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = A_61
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6685,plain,(
    ! [A_255,B_256] :
      ( k4_xboole_0(k1_tarski(A_255),B_256) = k1_tarski(A_255)
      | r2_hidden(A_255,B_256) ) ),
    inference(resolution,[status(thm)],[c_76,c_167])).

tff(c_38,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6780,plain,(
    ! [A_255,B_256] :
      ( k4_xboole_0(k1_tarski(A_255),k1_tarski(A_255)) = k3_xboole_0(k1_tarski(A_255),B_256)
      | r2_hidden(A_255,B_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6685,c_38])).

tff(c_6850,plain,(
    ! [A_257,B_258] :
      ( k3_xboole_0(k1_tarski(A_257),B_258) = k1_xboole_0
      | r2_hidden(A_257,B_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_6780])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_349,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_328])).

tff(c_6966,plain,(
    ! [B_258,A_257] :
      ( k4_xboole_0(B_258,k1_tarski(A_257)) = k5_xboole_0(B_258,k1_xboole_0)
      | r2_hidden(A_257,B_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6850,c_349])).

tff(c_7073,plain,(
    ! [B_259,A_260] :
      ( k4_xboole_0(B_259,k1_tarski(A_260)) = B_259
      | r2_hidden(A_260,B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_6966])).

tff(c_78,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_142,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_7195,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7073,c_142])).

tff(c_7252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_7195])).

tff(c_7253,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_70,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7321,plain,(
    ! [A_275,B_276] : k1_enumset1(A_275,A_275,B_276) = k2_tarski(A_275,B_276) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ! [E_31,A_25,C_27] : r2_hidden(E_31,k1_enumset1(A_25,E_31,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7339,plain,(
    ! [A_277,B_278] : r2_hidden(A_277,k2_tarski(A_277,B_278)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7321,c_50])).

tff(c_7342,plain,(
    ! [A_32] : r2_hidden(A_32,k1_tarski(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_7339])).

tff(c_7254,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7316,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7254,c_82])).

tff(c_7492,plain,(
    ! [D_291,B_292,A_293] :
      ( ~ r2_hidden(D_291,B_292)
      | ~ r2_hidden(D_291,k4_xboole_0(A_293,B_292)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7516,plain,(
    ! [D_299] :
      ( ~ r2_hidden(D_299,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_299,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7316,c_7492])).

tff(c_7520,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_7342,c_7516])).

tff(c_7524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7253,c_7520])).

tff(c_7525,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_7588,plain,(
    ! [A_318,B_319] : k1_enumset1(A_318,A_318,B_319) = k2_tarski(A_318,B_319) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [E_31,A_25,B_26] : r2_hidden(E_31,k1_enumset1(A_25,B_26,E_31)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7606,plain,(
    ! [B_320,A_321] : r2_hidden(B_320,k2_tarski(A_321,B_320)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7588,c_48])).

tff(c_7609,plain,(
    ! [A_32] : r2_hidden(A_32,k1_tarski(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_7606])).

tff(c_7526,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_84,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7632,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7526,c_84])).

tff(c_7655,plain,(
    ! [D_332,B_333,A_334] :
      ( ~ r2_hidden(D_332,B_333)
      | ~ r2_hidden(D_332,k4_xboole_0(A_334,B_333)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7677,plain,(
    ! [D_342] :
      ( ~ r2_hidden(D_342,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_342,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7632,c_7655])).

tff(c_7681,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_7609,c_7677])).

tff(c_7685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7525,c_7681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.34  % Computer   : n012.cluster.edu
% 0.11/0.34  % Model      : x86_64 x86_64
% 0.11/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.34  % Memory     : 8042.1875MB
% 0.11/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.34  % CPULimit   : 60
% 0.11/0.34  % DateTime   : Tue Dec  1 19:43:52 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.11  
% 5.33/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.12  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 5.33/2.12  
% 5.33/2.12  %Foreground sorts:
% 5.33/2.12  
% 5.33/2.12  
% 5.33/2.12  %Background operators:
% 5.33/2.12  
% 5.33/2.12  
% 5.33/2.12  %Foreground operators:
% 5.33/2.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.33/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.33/2.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.33/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.33/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.12  tff('#skF_7', type, '#skF_7': $i).
% 5.33/2.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.33/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.33/2.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.33/2.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.33/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.33/2.12  tff('#skF_6', type, '#skF_6': $i).
% 5.33/2.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.33/2.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.33/2.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.33/2.12  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.33/2.12  tff('#skF_8', type, '#skF_8': $i).
% 5.33/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.33/2.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.33/2.12  
% 5.33/2.13  tff(f_95, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.33/2.13  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.33/2.13  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.33/2.13  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.33/2.13  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.33/2.13  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.33/2.13  tff(f_89, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.33/2.13  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.33/2.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.33/2.13  tff(f_80, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.33/2.13  tff(f_82, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.33/2.13  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.33/2.13  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.33/2.13  tff(c_80, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.33/2.13  tff(c_105, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 5.33/2.13  tff(c_36, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.33/2.13  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.33/2.13  tff(c_145, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.33/2.13  tff(c_149, plain, (![B_10]: (k4_xboole_0(B_10, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_145])).
% 5.33/2.13  tff(c_228, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k4_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.33/2.13  tff(c_246, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_228])).
% 5.33/2.13  tff(c_250, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_246])).
% 5.33/2.13  tff(c_328, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.33/2.13  tff(c_340, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_250, c_328])).
% 5.33/2.13  tff(c_352, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_340])).
% 5.33/2.13  tff(c_76, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), B_39) | r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.33/2.13  tff(c_167, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=A_61 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.33/2.13  tff(c_6685, plain, (![A_255, B_256]: (k4_xboole_0(k1_tarski(A_255), B_256)=k1_tarski(A_255) | r2_hidden(A_255, B_256))), inference(resolution, [status(thm)], [c_76, c_167])).
% 5.33/2.13  tff(c_38, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.33/2.13  tff(c_6780, plain, (![A_255, B_256]: (k4_xboole_0(k1_tarski(A_255), k1_tarski(A_255))=k3_xboole_0(k1_tarski(A_255), B_256) | r2_hidden(A_255, B_256))), inference(superposition, [status(thm), theory('equality')], [c_6685, c_38])).
% 5.33/2.13  tff(c_6850, plain, (![A_257, B_258]: (k3_xboole_0(k1_tarski(A_257), B_258)=k1_xboole_0 | r2_hidden(A_257, B_258))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_6780])).
% 5.33/2.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.33/2.13  tff(c_349, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_328])).
% 5.33/2.13  tff(c_6966, plain, (![B_258, A_257]: (k4_xboole_0(B_258, k1_tarski(A_257))=k5_xboole_0(B_258, k1_xboole_0) | r2_hidden(A_257, B_258))), inference(superposition, [status(thm), theory('equality')], [c_6850, c_349])).
% 5.33/2.13  tff(c_7073, plain, (![B_259, A_260]: (k4_xboole_0(B_259, k1_tarski(A_260))=B_259 | r2_hidden(A_260, B_259))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_6966])).
% 5.33/2.13  tff(c_78, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.33/2.13  tff(c_142, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_78])).
% 5.33/2.13  tff(c_7195, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7073, c_142])).
% 5.33/2.13  tff(c_7252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_7195])).
% 5.33/2.13  tff(c_7253, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 5.33/2.13  tff(c_70, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.33/2.13  tff(c_7321, plain, (![A_275, B_276]: (k1_enumset1(A_275, A_275, B_276)=k2_tarski(A_275, B_276))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.33/2.13  tff(c_50, plain, (![E_31, A_25, C_27]: (r2_hidden(E_31, k1_enumset1(A_25, E_31, C_27)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.33/2.13  tff(c_7339, plain, (![A_277, B_278]: (r2_hidden(A_277, k2_tarski(A_277, B_278)))), inference(superposition, [status(thm), theory('equality')], [c_7321, c_50])).
% 5.33/2.13  tff(c_7342, plain, (![A_32]: (r2_hidden(A_32, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_7339])).
% 5.33/2.13  tff(c_7254, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_78])).
% 5.33/2.13  tff(c_82, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.33/2.13  tff(c_7316, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7254, c_82])).
% 5.33/2.13  tff(c_7492, plain, (![D_291, B_292, A_293]: (~r2_hidden(D_291, B_292) | ~r2_hidden(D_291, k4_xboole_0(A_293, B_292)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.33/2.13  tff(c_7516, plain, (![D_299]: (~r2_hidden(D_299, k1_tarski('#skF_8')) | ~r2_hidden(D_299, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_7316, c_7492])).
% 5.33/2.13  tff(c_7520, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_7342, c_7516])).
% 5.33/2.13  tff(c_7524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7253, c_7520])).
% 5.33/2.13  tff(c_7525, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_80])).
% 5.33/2.13  tff(c_7588, plain, (![A_318, B_319]: (k1_enumset1(A_318, A_318, B_319)=k2_tarski(A_318, B_319))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.33/2.13  tff(c_48, plain, (![E_31, A_25, B_26]: (r2_hidden(E_31, k1_enumset1(A_25, B_26, E_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.33/2.13  tff(c_7606, plain, (![B_320, A_321]: (r2_hidden(B_320, k2_tarski(A_321, B_320)))), inference(superposition, [status(thm), theory('equality')], [c_7588, c_48])).
% 5.33/2.13  tff(c_7609, plain, (![A_32]: (r2_hidden(A_32, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_7606])).
% 5.33/2.13  tff(c_7526, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_80])).
% 5.33/2.13  tff(c_84, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.33/2.13  tff(c_7632, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7526, c_84])).
% 5.33/2.13  tff(c_7655, plain, (![D_332, B_333, A_334]: (~r2_hidden(D_332, B_333) | ~r2_hidden(D_332, k4_xboole_0(A_334, B_333)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.33/2.13  tff(c_7677, plain, (![D_342]: (~r2_hidden(D_342, k1_tarski('#skF_8')) | ~r2_hidden(D_342, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_7632, c_7655])).
% 5.33/2.13  tff(c_7681, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_7609, c_7677])).
% 5.33/2.13  tff(c_7685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7525, c_7681])).
% 5.33/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.13  
% 5.33/2.13  Inference rules
% 5.33/2.13  ----------------------
% 5.33/2.13  #Ref     : 0
% 5.33/2.13  #Sup     : 1871
% 5.33/2.13  #Fact    : 0
% 5.33/2.13  #Define  : 0
% 5.33/2.13  #Split   : 2
% 5.33/2.13  #Chain   : 0
% 5.33/2.13  #Close   : 0
% 5.33/2.13  
% 5.33/2.13  Ordering : KBO
% 5.33/2.13  
% 5.33/2.13  Simplification rules
% 5.33/2.13  ----------------------
% 5.33/2.13  #Subsume      : 112
% 5.33/2.13  #Demod        : 2008
% 5.33/2.13  #Tautology    : 1318
% 5.33/2.13  #SimpNegUnit  : 1
% 5.33/2.13  #BackRed      : 4
% 5.33/2.13  
% 5.33/2.13  #Partial instantiations: 0
% 5.33/2.13  #Strategies tried      : 1
% 5.33/2.13  
% 5.33/2.13  Timing (in seconds)
% 5.33/2.13  ----------------------
% 5.33/2.13  Preprocessing        : 0.32
% 5.33/2.13  Parsing              : 0.16
% 5.33/2.13  CNF conversion       : 0.02
% 5.33/2.13  Main loop            : 1.03
% 5.33/2.13  Inferencing          : 0.31
% 5.33/2.13  Reduction            : 0.48
% 5.33/2.13  Demodulation         : 0.40
% 5.33/2.13  BG Simplification    : 0.04
% 5.33/2.13  Subsumption          : 0.15
% 5.33/2.13  Abstraction          : 0.06
% 5.33/2.13  MUC search           : 0.00
% 5.33/2.13  Cooper               : 0.00
% 5.33/2.13  Total                : 1.39
% 5.33/2.13  Index Insertion      : 0.00
% 5.33/2.13  Index Deletion       : 0.00
% 5.33/2.13  Index Matching       : 0.00
% 5.33/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
