%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:37 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   76 (  93 expanded)
%              Number of leaves         :   35 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 115 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

tff(c_68,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_30,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(k1_tarski(A_36),B_37)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_159,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_171,plain,(
    ! [A_64,B_65] :
      ( ~ r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_290,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(k1_tarski(A_90),B_91) = k1_xboole_0
      | r2_hidden(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_178,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_190,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_299,plain,(
    ! [B_91,A_90] :
      ( k4_xboole_0(B_91,k1_tarski(A_90)) = k5_xboole_0(B_91,k1_xboole_0)
      | r2_hidden(A_90,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_190])).

tff(c_398,plain,(
    ! [B_101,A_102] :
      ( k4_xboole_0(B_101,k1_tarski(A_102)) = B_101
      | r2_hidden(A_102,B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_299])).

tff(c_66,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_176,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_413,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_176])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_413])).

tff(c_422,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_56,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_129,plain,(
    ! [A_52,B_53] : k1_enumset1(A_52,A_52,B_53) = k2_tarski(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [E_25,A_19,B_20] : r2_hidden(E_25,k1_enumset1(A_19,B_20,E_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_147,plain,(
    ! [B_54,A_55] : r2_hidden(B_54,k2_tarski(A_55,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_34])).

tff(c_150,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_147])).

tff(c_423,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_70,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_473,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_70])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_484,plain,(
    ! [D_112] :
      ( ~ r2_hidden(D_112,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_112,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_6])).

tff(c_488,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_150,c_484])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_488])).

tff(c_497,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_501,plain,(
    ! [A_117,B_118] : k1_enumset1(A_117,A_117,B_118) = k2_tarski(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_519,plain,(
    ! [B_119,A_120] : r2_hidden(B_119,k2_tarski(A_120,B_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_34])).

tff(c_522,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_519])).

tff(c_498,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_533,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_72])).

tff(c_579,plain,(
    ! [D_136,B_137,A_138] :
      ( ~ r2_hidden(D_136,B_137)
      | ~ r2_hidden(D_136,k4_xboole_0(A_138,B_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_588,plain,(
    ! [D_139] :
      ( ~ r2_hidden(D_139,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_139,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_579])).

tff(c_592,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_522,c_588])).

tff(c_600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.46  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5
% 2.71/1.46  
% 2.71/1.46  %Foreground sorts:
% 2.71/1.46  
% 2.71/1.46  
% 2.71/1.46  %Background operators:
% 2.71/1.46  
% 2.71/1.46  
% 2.71/1.46  %Foreground operators:
% 2.71/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.46  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.71/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.46  tff('#skF_10', type, '#skF_10': $i).
% 2.71/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.71/1.46  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.71/1.46  tff('#skF_9', type, '#skF_9': $i).
% 2.71/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.46  
% 2.71/1.48  tff(f_97, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.71/1.48  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.71/1.48  tff(f_91, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.71/1.48  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.71/1.48  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.71/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.71/1.48  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.71/1.48  tff(f_80, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.71/1.48  tff(f_82, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.71/1.48  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.71/1.48  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.71/1.48  tff(c_68, plain, (~r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.71/1.48  tff(c_126, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_68])).
% 2.71/1.48  tff(c_30, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.48  tff(c_64, plain, (![A_36, B_37]: (r1_xboole_0(k1_tarski(A_36), B_37) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.71/1.48  tff(c_26, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.71/1.48  tff(c_159, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.48  tff(c_171, plain, (![A_64, B_65]: (~r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_159])).
% 2.71/1.48  tff(c_290, plain, (![A_90, B_91]: (k3_xboole_0(k1_tarski(A_90), B_91)=k1_xboole_0 | r2_hidden(A_90, B_91))), inference(resolution, [status(thm)], [c_64, c_171])).
% 2.71/1.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.48  tff(c_178, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.48  tff(c_190, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 2.71/1.48  tff(c_299, plain, (![B_91, A_90]: (k4_xboole_0(B_91, k1_tarski(A_90))=k5_xboole_0(B_91, k1_xboole_0) | r2_hidden(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_290, c_190])).
% 2.71/1.48  tff(c_398, plain, (![B_101, A_102]: (k4_xboole_0(B_101, k1_tarski(A_102))=B_101 | r2_hidden(A_102, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_299])).
% 2.71/1.48  tff(c_66, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.71/1.48  tff(c_176, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_66])).
% 2.71/1.48  tff(c_413, plain, (r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_398, c_176])).
% 2.71/1.48  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_413])).
% 2.71/1.48  tff(c_422, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_66])).
% 2.71/1.48  tff(c_56, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.48  tff(c_129, plain, (![A_52, B_53]: (k1_enumset1(A_52, A_52, B_53)=k2_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.48  tff(c_34, plain, (![E_25, A_19, B_20]: (r2_hidden(E_25, k1_enumset1(A_19, B_20, E_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.48  tff(c_147, plain, (![B_54, A_55]: (r2_hidden(B_54, k2_tarski(A_55, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_34])).
% 2.71/1.48  tff(c_150, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_147])).
% 2.71/1.48  tff(c_423, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 2.71/1.48  tff(c_70, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.71/1.48  tff(c_473, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_423, c_70])).
% 2.71/1.48  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.48  tff(c_484, plain, (![D_112]: (~r2_hidden(D_112, k1_tarski('#skF_10')) | ~r2_hidden(D_112, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_473, c_6])).
% 2.71/1.48  tff(c_488, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_150, c_484])).
% 2.71/1.48  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_488])).
% 2.71/1.48  tff(c_497, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 2.71/1.48  tff(c_501, plain, (![A_117, B_118]: (k1_enumset1(A_117, A_117, B_118)=k2_tarski(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.48  tff(c_519, plain, (![B_119, A_120]: (r2_hidden(B_119, k2_tarski(A_120, B_119)))), inference(superposition, [status(thm), theory('equality')], [c_501, c_34])).
% 2.71/1.48  tff(c_522, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_519])).
% 2.71/1.48  tff(c_498, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 2.71/1.48  tff(c_72, plain, (~r2_hidden('#skF_8', '#skF_7') | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.71/1.48  tff(c_533, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_498, c_72])).
% 2.71/1.48  tff(c_579, plain, (![D_136, B_137, A_138]: (~r2_hidden(D_136, B_137) | ~r2_hidden(D_136, k4_xboole_0(A_138, B_137)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.48  tff(c_588, plain, (![D_139]: (~r2_hidden(D_139, k1_tarski('#skF_10')) | ~r2_hidden(D_139, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_579])).
% 2.71/1.48  tff(c_592, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_522, c_588])).
% 2.71/1.48  tff(c_600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_592])).
% 2.71/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.48  
% 2.71/1.48  Inference rules
% 2.71/1.48  ----------------------
% 2.71/1.48  #Ref     : 0
% 2.71/1.48  #Sup     : 124
% 2.71/1.48  #Fact    : 0
% 2.71/1.48  #Define  : 0
% 2.71/1.48  #Split   : 3
% 2.71/1.48  #Chain   : 0
% 2.71/1.48  #Close   : 0
% 2.71/1.48  
% 2.71/1.48  Ordering : KBO
% 2.71/1.48  
% 2.71/1.48  Simplification rules
% 2.71/1.48  ----------------------
% 2.71/1.48  #Subsume      : 17
% 2.71/1.48  #Demod        : 16
% 2.71/1.48  #Tautology    : 59
% 2.71/1.48  #SimpNegUnit  : 1
% 2.71/1.48  #BackRed      : 0
% 2.71/1.48  
% 2.71/1.48  #Partial instantiations: 0
% 2.71/1.48  #Strategies tried      : 1
% 2.71/1.48  
% 2.71/1.48  Timing (in seconds)
% 2.71/1.48  ----------------------
% 2.71/1.48  Preprocessing        : 0.37
% 2.71/1.48  Parsing              : 0.21
% 2.71/1.48  CNF conversion       : 0.03
% 2.71/1.48  Main loop            : 0.27
% 2.71/1.48  Inferencing          : 0.10
% 2.71/1.48  Reduction            : 0.08
% 2.71/1.48  Demodulation         : 0.06
% 2.71/1.48  BG Simplification    : 0.02
% 2.71/1.48  Subsumption          : 0.05
% 2.71/1.48  Abstraction          : 0.02
% 2.71/1.48  MUC search           : 0.00
% 2.71/1.48  Cooper               : 0.00
% 2.71/1.48  Total                : 0.67
% 2.71/1.48  Index Insertion      : 0.00
% 2.71/1.48  Index Deletion       : 0.00
% 2.71/1.48  Index Matching       : 0.00
% 2.71/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
