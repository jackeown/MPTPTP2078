%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:37 EST 2020

% Result     : Theorem 9.48s
% Output     : CNFRefutation 9.48s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 120 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 157 expanded)
%              Number of equality atoms :   47 (  86 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_42,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [B_38,C_39] :
      ( k4_xboole_0(k2_tarski(B_38,B_38),C_39) = k1_tarski(B_38)
      | r2_hidden(B_38,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_65,plain,(
    ! [B_38,C_39] :
      ( k4_xboole_0(k1_tarski(B_38),C_39) = k1_tarski(B_38)
      | r2_hidden(B_38,C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_48])).

tff(c_26,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_149,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,k3_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_34])).

tff(c_181,plain,(
    ! [A_63,B_64] : k3_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_149])).

tff(c_208,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_181])).

tff(c_214,plain,(
    ! [A_15] : k3_xboole_0(A_15,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_208])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3369,plain,(
    ! [A_212,B_213,C_214] :
      ( ~ r2_hidden('#skF_1'(A_212,B_213,C_214),B_213)
      | r2_hidden('#skF_2'(A_212,B_213,C_214),C_214)
      | k4_xboole_0(A_212,B_213) = C_214 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4986,plain,(
    ! [A_281,C_282] :
      ( r2_hidden('#skF_2'(A_281,A_281,C_282),C_282)
      | k4_xboole_0(A_281,A_281) = C_282 ) ),
    inference(resolution,[status(thm)],[c_20,c_3369])).

tff(c_167,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_143])).

tff(c_736,plain,(
    ! [A_104,B_105,C_106] : k4_xboole_0(k4_xboole_0(A_104,B_105),C_106) = k4_xboole_0(A_104,k2_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [C_42,B_41] : ~ r2_hidden(C_42,k4_xboole_0(B_41,k1_tarski(C_42))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_841,plain,(
    ! [C_107,A_108,B_109] : ~ r2_hidden(C_107,k4_xboole_0(A_108,k2_xboole_0(B_109,k1_tarski(C_107)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_54])).

tff(c_856,plain,(
    ! [C_107,A_15] : ~ r2_hidden(C_107,k4_xboole_0(A_15,A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_841])).

tff(c_5149,plain,(
    ! [A_284,A_283] : k4_xboole_0(A_284,A_284) = k4_xboole_0(A_283,A_283) ),
    inference(resolution,[status(thm)],[c_4986,c_856])).

tff(c_5412,plain,(
    ! [A_283,A_284] : k4_xboole_0(A_283,k4_xboole_0(A_284,A_284)) = k3_xboole_0(A_283,A_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_5149,c_34])).

tff(c_5492,plain,(
    ! [A_283,A_284] : k4_xboole_0(A_283,k4_xboole_0(A_284,A_284)) = A_283 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_5412])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_161,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_36,plain,(
    ! [A_27,B_28,C_29] : k4_xboole_0(k3_xboole_0(A_27,B_28),C_29) = k3_xboole_0(A_27,k4_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5469,plain,(
    ! [A_283,A_27,B_28] : k4_xboole_0(A_283,A_283) = k3_xboole_0(A_27,k4_xboole_0(B_28,k3_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5149])).

tff(c_6280,plain,(
    ! [A_294,A_295,B_296] : k4_xboole_0(A_294,A_294) = k3_xboole_0(A_295,k4_xboole_0(B_296,A_295)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_5469])).

tff(c_32,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6548,plain,(
    ! [A_295,B_296,A_294] : k4_xboole_0(A_295,k4_xboole_0(B_296,A_295)) = k4_xboole_0(A_295,k4_xboole_0(A_294,A_294)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6280,c_32])).

tff(c_6927,plain,(
    ! [A_300,B_301] : k4_xboole_0(A_300,k4_xboole_0(B_301,A_300)) = A_300 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5492,c_6548])).

tff(c_15695,plain,(
    ! [C_387,B_388] :
      ( k4_xboole_0(C_387,k1_tarski(B_388)) = C_387
      | r2_hidden(B_388,C_387) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_6927])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_15902,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15695,c_121])).

tff(c_15989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_15902])).

tff(c_15990,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_15991,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_4')) != '#skF_3'
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16061,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15991,c_62])).

tff(c_16074,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16061,c_54])).

tff(c_16079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15990,c_16074])).

tff(c_16080,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_16081,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16149,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16081,c_64])).

tff(c_16162,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16149,c_54])).

tff(c_16167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16080,c_16162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.48/3.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.48/3.24  
% 9.48/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.48/3.25  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 9.48/3.25  
% 9.48/3.25  %Foreground sorts:
% 9.48/3.25  
% 9.48/3.25  
% 9.48/3.25  %Background operators:
% 9.48/3.25  
% 9.48/3.25  
% 9.48/3.25  %Foreground operators:
% 9.48/3.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.48/3.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.48/3.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.48/3.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.48/3.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.48/3.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.48/3.25  tff('#skF_5', type, '#skF_5': $i).
% 9.48/3.25  tff('#skF_6', type, '#skF_6': $i).
% 9.48/3.25  tff('#skF_3', type, '#skF_3': $i).
% 9.48/3.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.48/3.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.48/3.25  tff('#skF_4', type, '#skF_4': $i).
% 9.48/3.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.48/3.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.48/3.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.48/3.25  
% 9.48/3.26  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 9.48/3.26  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.48/3.26  tff(f_68, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 9.48/3.26  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 9.48/3.26  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.48/3.26  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.48/3.26  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.48/3.26  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.48/3.26  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 9.48/3.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.48/3.26  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 9.48/3.26  tff(c_60, plain, (~r2_hidden('#skF_4', '#skF_3') | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.48/3.26  tff(c_75, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 9.48/3.26  tff(c_42, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.48/3.26  tff(c_48, plain, (![B_38, C_39]: (k4_xboole_0(k2_tarski(B_38, B_38), C_39)=k1_tarski(B_38) | r2_hidden(B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.48/3.26  tff(c_65, plain, (![B_38, C_39]: (k4_xboole_0(k1_tarski(B_38), C_39)=k1_tarski(B_38) | r2_hidden(B_38, C_39))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_48])).
% 9.48/3.26  tff(c_26, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.48/3.26  tff(c_34, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.48/3.26  tff(c_143, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.48/3.26  tff(c_149, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, k3_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_34])).
% 9.48/3.26  tff(c_181, plain, (![A_63, B_64]: (k3_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_149])).
% 9.48/3.26  tff(c_208, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k3_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_26, c_181])).
% 9.48/3.26  tff(c_214, plain, (![A_15]: (k3_xboole_0(A_15, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_208])).
% 9.48/3.26  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.48/3.26  tff(c_3369, plain, (![A_212, B_213, C_214]: (~r2_hidden('#skF_1'(A_212, B_213, C_214), B_213) | r2_hidden('#skF_2'(A_212, B_213, C_214), C_214) | k4_xboole_0(A_212, B_213)=C_214)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.48/3.26  tff(c_4986, plain, (![A_281, C_282]: (r2_hidden('#skF_2'(A_281, A_281, C_282), C_282) | k4_xboole_0(A_281, A_281)=C_282)), inference(resolution, [status(thm)], [c_20, c_3369])).
% 9.48/3.26  tff(c_167, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k4_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_26, c_143])).
% 9.48/3.26  tff(c_736, plain, (![A_104, B_105, C_106]: (k4_xboole_0(k4_xboole_0(A_104, B_105), C_106)=k4_xboole_0(A_104, k2_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.48/3.26  tff(c_54, plain, (![C_42, B_41]: (~r2_hidden(C_42, k4_xboole_0(B_41, k1_tarski(C_42))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.48/3.26  tff(c_841, plain, (![C_107, A_108, B_109]: (~r2_hidden(C_107, k4_xboole_0(A_108, k2_xboole_0(B_109, k1_tarski(C_107)))))), inference(superposition, [status(thm), theory('equality')], [c_736, c_54])).
% 9.48/3.26  tff(c_856, plain, (![C_107, A_15]: (~r2_hidden(C_107, k4_xboole_0(A_15, A_15)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_841])).
% 9.48/3.26  tff(c_5149, plain, (![A_284, A_283]: (k4_xboole_0(A_284, A_284)=k4_xboole_0(A_283, A_283))), inference(resolution, [status(thm)], [c_4986, c_856])).
% 9.48/3.26  tff(c_5412, plain, (![A_283, A_284]: (k4_xboole_0(A_283, k4_xboole_0(A_284, A_284))=k3_xboole_0(A_283, A_283))), inference(superposition, [status(thm), theory('equality')], [c_5149, c_34])).
% 9.48/3.26  tff(c_5492, plain, (![A_283, A_284]: (k4_xboole_0(A_283, k4_xboole_0(A_284, A_284))=A_283)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_5412])).
% 9.48/3.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.48/3.26  tff(c_161, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_143])).
% 9.48/3.26  tff(c_36, plain, (![A_27, B_28, C_29]: (k4_xboole_0(k3_xboole_0(A_27, B_28), C_29)=k3_xboole_0(A_27, k4_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.48/3.26  tff(c_5469, plain, (![A_283, A_27, B_28]: (k4_xboole_0(A_283, A_283)=k3_xboole_0(A_27, k4_xboole_0(B_28, k3_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_5149])).
% 9.48/3.26  tff(c_6280, plain, (![A_294, A_295, B_296]: (k4_xboole_0(A_294, A_294)=k3_xboole_0(A_295, k4_xboole_0(B_296, A_295)))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_5469])).
% 9.48/3.26  tff(c_32, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.48/3.26  tff(c_6548, plain, (![A_295, B_296, A_294]: (k4_xboole_0(A_295, k4_xboole_0(B_296, A_295))=k4_xboole_0(A_295, k4_xboole_0(A_294, A_294)))), inference(superposition, [status(thm), theory('equality')], [c_6280, c_32])).
% 9.48/3.26  tff(c_6927, plain, (![A_300, B_301]: (k4_xboole_0(A_300, k4_xboole_0(B_301, A_300))=A_300)), inference(demodulation, [status(thm), theory('equality')], [c_5492, c_6548])).
% 9.48/3.26  tff(c_15695, plain, (![C_387, B_388]: (k4_xboole_0(C_387, k1_tarski(B_388))=C_387 | r2_hidden(B_388, C_387))), inference(superposition, [status(thm), theory('equality')], [c_65, c_6927])).
% 9.48/3.26  tff(c_58, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.48/3.26  tff(c_121, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_58])).
% 9.48/3.26  tff(c_15902, plain, (r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15695, c_121])).
% 9.48/3.26  tff(c_15989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_15902])).
% 9.48/3.26  tff(c_15990, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 9.48/3.26  tff(c_15991, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_58])).
% 9.48/3.26  tff(c_62, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))!='#skF_3' | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.48/3.26  tff(c_16061, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15991, c_62])).
% 9.48/3.26  tff(c_16074, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16061, c_54])).
% 9.48/3.26  tff(c_16079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15990, c_16074])).
% 9.48/3.26  tff(c_16080, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 9.48/3.26  tff(c_16081, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 9.48/3.26  tff(c_64, plain, (~r2_hidden('#skF_4', '#skF_3') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.48/3.26  tff(c_16149, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16081, c_64])).
% 9.48/3.26  tff(c_16162, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16149, c_54])).
% 9.48/3.26  tff(c_16167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16080, c_16162])).
% 9.48/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.48/3.26  
% 9.48/3.26  Inference rules
% 9.48/3.26  ----------------------
% 9.48/3.26  #Ref     : 0
% 9.48/3.26  #Sup     : 4234
% 9.48/3.26  #Fact    : 0
% 9.48/3.26  #Define  : 0
% 9.48/3.26  #Split   : 2
% 9.48/3.26  #Chain   : 0
% 9.48/3.26  #Close   : 0
% 9.48/3.26  
% 9.48/3.26  Ordering : KBO
% 9.48/3.26  
% 9.48/3.26  Simplification rules
% 9.48/3.26  ----------------------
% 9.48/3.26  #Subsume      : 1218
% 9.48/3.26  #Demod        : 2202
% 9.48/3.26  #Tautology    : 1084
% 9.48/3.26  #SimpNegUnit  : 58
% 9.48/3.26  #BackRed      : 11
% 9.48/3.26  
% 9.48/3.26  #Partial instantiations: 0
% 9.48/3.26  #Strategies tried      : 1
% 9.48/3.26  
% 9.48/3.26  Timing (in seconds)
% 9.48/3.26  ----------------------
% 9.48/3.26  Preprocessing        : 0.32
% 9.48/3.26  Parsing              : 0.17
% 9.48/3.26  CNF conversion       : 0.02
% 9.48/3.26  Main loop            : 2.17
% 9.48/3.26  Inferencing          : 0.54
% 9.48/3.26  Reduction            : 1.04
% 9.48/3.26  Demodulation         : 0.87
% 9.48/3.26  BG Simplification    : 0.08
% 9.48/3.26  Subsumption          : 0.39
% 9.48/3.26  Abstraction          : 0.10
% 9.48/3.26  MUC search           : 0.00
% 9.48/3.26  Cooper               : 0.00
% 9.48/3.26  Total                : 2.53
% 9.48/3.27  Index Insertion      : 0.00
% 9.48/3.27  Index Deletion       : 0.00
% 9.48/3.27  Index Matching       : 0.00
% 9.48/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
