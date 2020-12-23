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

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   74 (  95 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 119 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
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

tff(c_64,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_123,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_28,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_125,plain,(
    ! [A_44,B_45] :
      ( r1_xboole_0(k1_tarski(A_44),B_45)
      | r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(k1_tarski(A_44),B_45) = k1_xboole_0
      | r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_125,c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_209,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(B_66,A_65)) = k4_xboole_0(A_65,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_166])).

tff(c_222,plain,(
    ! [B_45,A_44] :
      ( k4_xboole_0(B_45,k1_tarski(A_44)) = k5_xboole_0(B_45,k1_xboole_0)
      | r2_hidden(A_44,B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_209])).

tff(c_291,plain,(
    ! [B_72,A_73] :
      ( k4_xboole_0(B_72,k1_tarski(A_73)) = B_72
      | r2_hidden(A_73,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_222])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_164,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_303,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_164])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_303])).

tff(c_312,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_54,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    ! [A_46,B_47] : k1_enumset1(A_46,A_46,B_47) = k2_tarski(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_148,plain,(
    ! [B_48,A_49] : r2_hidden(B_48,k2_tarski(A_49,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_32])).

tff(c_151,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_148])).

tff(c_313,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_314,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_314])).

tff(c_321,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_332,plain,(
    ! [D_74,B_75,A_76] :
      ( ~ r2_hidden(D_74,B_75)
      | ~ r2_hidden(D_74,k4_xboole_0(A_76,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_339,plain,(
    ! [D_77] :
      ( ~ r2_hidden(D_77,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_77,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_332])).

tff(c_343,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_151,c_339])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_343])).

tff(c_348,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_367,plain,(
    ! [A_82,B_83] : k1_enumset1(A_82,A_82,B_83) = k2_tarski(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_385,plain,(
    ! [B_84,A_85] : r2_hidden(B_84,k2_tarski(A_85,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_32])).

tff(c_388,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_385])).

tff(c_349,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_350,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_350])).

tff(c_353,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_420,plain,(
    ! [D_96,B_97,A_98] :
      ( ~ r2_hidden(D_96,B_97)
      | ~ r2_hidden(D_96,k4_xboole_0(A_98,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_425,plain,(
    ! [D_99] :
      ( ~ r2_hidden(D_99,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_99,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_420])).

tff(c_429,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_388,c_425])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:34:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.34  
% 2.13/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.35  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.13/1.35  
% 2.13/1.35  %Foreground sorts:
% 2.13/1.35  
% 2.13/1.35  
% 2.13/1.35  %Background operators:
% 2.13/1.35  
% 2.13/1.35  
% 2.13/1.35  %Foreground operators:
% 2.13/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.13/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.13/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.13/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.13/1.35  
% 2.45/1.36  tff(f_77, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.45/1.36  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.45/1.36  tff(f_71, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.45/1.36  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.45/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.45/1.36  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.45/1.36  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.45/1.36  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.45/1.36  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.45/1.36  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.45/1.36  tff(c_64, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.45/1.36  tff(c_123, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_64])).
% 2.45/1.36  tff(c_28, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.36  tff(c_125, plain, (![A_44, B_45]: (r1_xboole_0(k1_tarski(A_44), B_45) | r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.36  tff(c_22, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.36  tff(c_129, plain, (![A_44, B_45]: (k3_xboole_0(k1_tarski(A_44), B_45)=k1_xboole_0 | r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_125, c_22])).
% 2.45/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.36  tff(c_166, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.36  tff(c_209, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(B_66, A_65))=k4_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_2, c_166])).
% 2.45/1.36  tff(c_222, plain, (![B_45, A_44]: (k4_xboole_0(B_45, k1_tarski(A_44))=k5_xboole_0(B_45, k1_xboole_0) | r2_hidden(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_129, c_209])).
% 2.45/1.36  tff(c_291, plain, (![B_72, A_73]: (k4_xboole_0(B_72, k1_tarski(A_73))=B_72 | r2_hidden(A_73, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_222])).
% 2.45/1.36  tff(c_62, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.45/1.36  tff(c_164, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_62])).
% 2.45/1.36  tff(c_303, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_291, c_164])).
% 2.45/1.36  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_303])).
% 2.45/1.36  tff(c_312, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 2.45/1.36  tff(c_54, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.45/1.36  tff(c_130, plain, (![A_46, B_47]: (k1_enumset1(A_46, A_46, B_47)=k2_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.36  tff(c_32, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.45/1.36  tff(c_148, plain, (![B_48, A_49]: (r2_hidden(B_48, k2_tarski(A_49, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_32])).
% 2.45/1.36  tff(c_151, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_148])).
% 2.45/1.36  tff(c_313, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 2.45/1.36  tff(c_66, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.45/1.36  tff(c_314, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_66])).
% 2.45/1.36  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_314])).
% 2.45/1.36  tff(c_321, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 2.45/1.36  tff(c_332, plain, (![D_74, B_75, A_76]: (~r2_hidden(D_74, B_75) | ~r2_hidden(D_74, k4_xboole_0(A_76, B_75)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.36  tff(c_339, plain, (![D_77]: (~r2_hidden(D_77, k1_tarski('#skF_8')) | ~r2_hidden(D_77, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_321, c_332])).
% 2.45/1.36  tff(c_343, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_151, c_339])).
% 2.45/1.36  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_312, c_343])).
% 2.45/1.36  tff(c_348, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 2.45/1.36  tff(c_367, plain, (![A_82, B_83]: (k1_enumset1(A_82, A_82, B_83)=k2_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.36  tff(c_385, plain, (![B_84, A_85]: (r2_hidden(B_84, k2_tarski(A_85, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_367, c_32])).
% 2.45/1.36  tff(c_388, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_385])).
% 2.45/1.36  tff(c_349, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 2.45/1.36  tff(c_68, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.45/1.36  tff(c_350, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_68])).
% 2.45/1.36  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_350])).
% 2.45/1.36  tff(c_353, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_68])).
% 2.45/1.36  tff(c_420, plain, (![D_96, B_97, A_98]: (~r2_hidden(D_96, B_97) | ~r2_hidden(D_96, k4_xboole_0(A_98, B_97)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.36  tff(c_425, plain, (![D_99]: (~r2_hidden(D_99, k1_tarski('#skF_8')) | ~r2_hidden(D_99, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_420])).
% 2.45/1.36  tff(c_429, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_388, c_425])).
% 2.45/1.36  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_429])).
% 2.45/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.36  
% 2.45/1.36  Inference rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Ref     : 0
% 2.45/1.36  #Sup     : 83
% 2.45/1.36  #Fact    : 0
% 2.45/1.36  #Define  : 0
% 2.45/1.36  #Split   : 4
% 2.45/1.36  #Chain   : 0
% 2.45/1.36  #Close   : 0
% 2.45/1.36  
% 2.45/1.36  Ordering : KBO
% 2.45/1.36  
% 2.45/1.36  Simplification rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Subsume      : 6
% 2.45/1.36  #Demod        : 19
% 2.45/1.36  #Tautology    : 56
% 2.45/1.36  #SimpNegUnit  : 1
% 2.45/1.36  #BackRed      : 0
% 2.45/1.36  
% 2.45/1.36  #Partial instantiations: 0
% 2.45/1.36  #Strategies tried      : 1
% 2.45/1.36  
% 2.45/1.36  Timing (in seconds)
% 2.45/1.36  ----------------------
% 2.45/1.37  Preprocessing        : 0.33
% 2.45/1.37  Parsing              : 0.17
% 2.45/1.37  CNF conversion       : 0.03
% 2.45/1.37  Main loop            : 0.24
% 2.45/1.37  Inferencing          : 0.08
% 2.45/1.37  Reduction            : 0.08
% 2.45/1.37  Demodulation         : 0.06
% 2.45/1.37  BG Simplification    : 0.02
% 2.45/1.37  Subsumption          : 0.04
% 2.45/1.37  Abstraction          : 0.02
% 2.45/1.37  MUC search           : 0.00
% 2.45/1.37  Cooper               : 0.00
% 2.45/1.37  Total                : 0.60
% 2.45/1.37  Index Insertion      : 0.00
% 2.45/1.37  Index Deletion       : 0.00
% 2.45/1.37  Index Matching       : 0.00
% 2.45/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
