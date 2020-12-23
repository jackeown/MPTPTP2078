%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:39 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 111 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

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

tff(f_35,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_155,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,k4_xboole_0(B_68,k1_tarski(C_69)))
      | r2_hidden(C_69,A_67)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_121,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_28,c_116])).

tff(c_159,plain,(
    ! [B_68,C_69] :
      ( k4_xboole_0(B_68,k1_tarski(C_69)) = B_68
      | r2_hidden(C_69,B_68)
      | ~ r1_tarski(B_68,B_68) ) ),
    inference(resolution,[status(thm)],[c_155,c_121])).

tff(c_185,plain,(
    ! [B_74,C_75] :
      ( k4_xboole_0(B_74,k1_tarski(C_75)) = B_74
      | r2_hidden(C_75,B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_159])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_103,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_206,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_103])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_206])).

tff(c_220,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_54,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_85,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [E_19,A_13,C_15] : r2_hidden(E_19,k1_enumset1(A_13,E_19,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_230,plain,(
    ! [A_76,B_77] : r2_hidden(A_76,k2_tarski(A_76,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_34])).

tff(c_233,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_230])).

tff(c_221,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_275,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_66])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_290,plain,(
    ! [D_92] :
      ( ~ r2_hidden(D_92,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_92,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_4])).

tff(c_294,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_233,c_290])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_294])).

tff(c_299,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_301,plain,(
    ! [A_93,B_94] : k1_enumset1(A_93,A_93,B_94) = k2_tarski(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_319,plain,(
    ! [B_95,A_96] : r2_hidden(B_95,k2_tarski(A_96,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_32])).

tff(c_322,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_319])).

tff(c_300,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_332,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_68])).

tff(c_344,plain,(
    ! [D_103,B_104,A_105] :
      ( ~ r2_hidden(D_103,B_104)
      | ~ r2_hidden(D_103,k4_xboole_0(A_105,B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_348,plain,(
    ! [D_106] :
      ( ~ r2_hidden(D_106,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_106,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_344])).

tff(c_352,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_322,c_348])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.12/1.28  
% 2.12/1.28  %Foreground sorts:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Background operators:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Foreground operators:
% 2.12/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.12/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.12/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.12/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.12/1.28  
% 2.12/1.30  tff(f_78, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.12/1.30  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.30  tff(f_72, axiom, (![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_zfmisc_1)).
% 2.12/1.30  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.12/1.30  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.30  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.12/1.30  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.12/1.30  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.12/1.30  tff(c_64, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.30  tff(c_84, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_64])).
% 2.12/1.30  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.30  tff(c_155, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, k4_xboole_0(B_68, k1_tarski(C_69))) | r2_hidden(C_69, A_67) | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.30  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.30  tff(c_116, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.30  tff(c_121, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_28, c_116])).
% 2.12/1.30  tff(c_159, plain, (![B_68, C_69]: (k4_xboole_0(B_68, k1_tarski(C_69))=B_68 | r2_hidden(C_69, B_68) | ~r1_tarski(B_68, B_68))), inference(resolution, [status(thm)], [c_155, c_121])).
% 2.12/1.30  tff(c_185, plain, (![B_74, C_75]: (k4_xboole_0(B_74, k1_tarski(C_75))=B_74 | r2_hidden(C_75, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_159])).
% 2.12/1.30  tff(c_62, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.30  tff(c_103, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_62])).
% 2.12/1.30  tff(c_206, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_185, c_103])).
% 2.12/1.30  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_206])).
% 2.12/1.30  tff(c_220, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 2.12/1.30  tff(c_54, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.12/1.30  tff(c_85, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.30  tff(c_34, plain, (![E_19, A_13, C_15]: (r2_hidden(E_19, k1_enumset1(A_13, E_19, C_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.12/1.30  tff(c_230, plain, (![A_76, B_77]: (r2_hidden(A_76, k2_tarski(A_76, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_34])).
% 2.12/1.30  tff(c_233, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_230])).
% 2.12/1.30  tff(c_221, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 2.12/1.30  tff(c_66, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.30  tff(c_275, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_66])).
% 2.12/1.30  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.30  tff(c_290, plain, (![D_92]: (~r2_hidden(D_92, k1_tarski('#skF_8')) | ~r2_hidden(D_92, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_275, c_4])).
% 2.12/1.30  tff(c_294, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_233, c_290])).
% 2.12/1.30  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_294])).
% 2.12/1.30  tff(c_299, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 2.12/1.30  tff(c_301, plain, (![A_93, B_94]: (k1_enumset1(A_93, A_93, B_94)=k2_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.30  tff(c_32, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.12/1.30  tff(c_319, plain, (![B_95, A_96]: (r2_hidden(B_95, k2_tarski(A_96, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_301, c_32])).
% 2.12/1.30  tff(c_322, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_319])).
% 2.12/1.30  tff(c_300, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 2.12/1.30  tff(c_68, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.30  tff(c_332, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_300, c_68])).
% 2.12/1.30  tff(c_344, plain, (![D_103, B_104, A_105]: (~r2_hidden(D_103, B_104) | ~r2_hidden(D_103, k4_xboole_0(A_105, B_104)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.30  tff(c_348, plain, (![D_106]: (~r2_hidden(D_106, k1_tarski('#skF_8')) | ~r2_hidden(D_106, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_344])).
% 2.12/1.30  tff(c_352, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_322, c_348])).
% 2.12/1.30  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_352])).
% 2.12/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  Inference rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Ref     : 0
% 2.12/1.30  #Sup     : 63
% 2.12/1.30  #Fact    : 0
% 2.12/1.30  #Define  : 0
% 2.12/1.30  #Split   : 2
% 2.12/1.30  #Chain   : 0
% 2.12/1.30  #Close   : 0
% 2.12/1.30  
% 2.12/1.30  Ordering : KBO
% 2.12/1.30  
% 2.12/1.30  Simplification rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Subsume      : 5
% 2.12/1.30  #Demod        : 18
% 2.12/1.30  #Tautology    : 42
% 2.12/1.30  #SimpNegUnit  : 1
% 2.12/1.30  #BackRed      : 0
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.30  #Strategies tried      : 1
% 2.12/1.30  
% 2.12/1.30  Timing (in seconds)
% 2.12/1.30  ----------------------
% 2.37/1.30  Preprocessing        : 0.31
% 2.37/1.30  Parsing              : 0.15
% 2.37/1.30  CNF conversion       : 0.03
% 2.37/1.30  Main loop            : 0.21
% 2.37/1.30  Inferencing          : 0.08
% 2.37/1.30  Reduction            : 0.07
% 2.37/1.30  Demodulation         : 0.05
% 2.37/1.30  BG Simplification    : 0.02
% 2.37/1.30  Subsumption          : 0.04
% 2.37/1.30  Abstraction          : 0.01
% 2.37/1.30  MUC search           : 0.00
% 2.37/1.30  Cooper               : 0.00
% 2.37/1.30  Total                : 0.56
% 2.37/1.30  Index Insertion      : 0.00
% 2.37/1.30  Index Deletion       : 0.00
% 2.37/1.30  Index Matching       : 0.00
% 2.37/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
