%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:41 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   66 (  84 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 108 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_114,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [B_53,A_54] :
      ( r1_xboole_0(B_53,k1_tarski(A_54))
      | r2_hidden(A_54,B_53) ) ),
    inference(resolution,[status(thm)],[c_114,c_20])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    ! [B_70,A_71] :
      ( k4_xboole_0(B_70,k1_tarski(A_71)) = B_70
      | r2_hidden(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_127,c_24])).

tff(c_60,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_143,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_180,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_143])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_180])).

tff(c_190,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_52,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,(
    ! [B_42,A_43] : r2_hidden(B_42,k2_tarski(A_43,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_30])).

tff(c_102,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_191,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_192,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_192])).

tff(c_199,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_210,plain,(
    ! [D_72,B_73,A_74] :
      ( ~ r2_hidden(D_72,B_73)
      | ~ r2_hidden(D_72,k4_xboole_0(A_74,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_217,plain,(
    ! [D_75] :
      ( ~ r2_hidden(D_75,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_75,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_210])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_217])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_221])).

tff(c_226,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_242,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [E_19,A_13,C_15] : r2_hidden(E_19,k1_enumset1(A_13,E_19,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_260,plain,(
    ! [A_93,B_94] : r2_hidden(A_93,k2_tarski(A_93,B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_32])).

tff(c_263,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_260])).

tff(c_227,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_266,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_66])).

tff(c_301,plain,(
    ! [D_104,B_105,A_106] :
      ( ~ r2_hidden(D_104,B_105)
      | ~ r2_hidden(D_104,k4_xboole_0(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_305,plain,(
    ! [D_107] :
      ( ~ r2_hidden(D_107,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_107,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_301])).

tff(c_309,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_263,c_305])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.09/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.09/1.30  
% 2.09/1.31  tff(f_77, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.09/1.31  tff(f_71, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.09/1.31  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.09/1.31  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.09/1.31  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.31  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.31  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.09/1.31  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.09/1.31  tff(c_62, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.31  tff(c_76, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 2.09/1.31  tff(c_114, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.31  tff(c_20, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.31  tff(c_127, plain, (![B_53, A_54]: (r1_xboole_0(B_53, k1_tarski(A_54)) | r2_hidden(A_54, B_53))), inference(resolution, [status(thm)], [c_114, c_20])).
% 2.09/1.31  tff(c_24, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.31  tff(c_166, plain, (![B_70, A_71]: (k4_xboole_0(B_70, k1_tarski(A_71))=B_70 | r2_hidden(A_71, B_70))), inference(resolution, [status(thm)], [c_127, c_24])).
% 2.09/1.31  tff(c_60, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.31  tff(c_143, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_60])).
% 2.09/1.31  tff(c_180, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_166, c_143])).
% 2.09/1.31  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_180])).
% 2.09/1.31  tff(c_190, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 2.09/1.31  tff(c_52, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.31  tff(c_81, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.31  tff(c_30, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.31  tff(c_99, plain, (![B_42, A_43]: (r2_hidden(B_42, k2_tarski(A_43, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_30])).
% 2.09/1.31  tff(c_102, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_99])).
% 2.09/1.31  tff(c_191, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 2.09/1.31  tff(c_64, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.31  tff(c_192, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_64])).
% 2.09/1.31  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_192])).
% 2.09/1.31  tff(c_199, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_64])).
% 2.09/1.31  tff(c_210, plain, (![D_72, B_73, A_74]: (~r2_hidden(D_72, B_73) | ~r2_hidden(D_72, k4_xboole_0(A_74, B_73)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.31  tff(c_217, plain, (![D_75]: (~r2_hidden(D_75, k1_tarski('#skF_8')) | ~r2_hidden(D_75, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_210])).
% 2.09/1.31  tff(c_221, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_102, c_217])).
% 2.09/1.31  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_221])).
% 2.09/1.31  tff(c_226, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 2.09/1.31  tff(c_242, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.31  tff(c_32, plain, (![E_19, A_13, C_15]: (r2_hidden(E_19, k1_enumset1(A_13, E_19, C_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.31  tff(c_260, plain, (![A_93, B_94]: (r2_hidden(A_93, k2_tarski(A_93, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_242, c_32])).
% 2.09/1.31  tff(c_263, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_260])).
% 2.09/1.31  tff(c_227, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 2.09/1.31  tff(c_66, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.31  tff(c_266, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_66])).
% 2.09/1.31  tff(c_301, plain, (![D_104, B_105, A_106]: (~r2_hidden(D_104, B_105) | ~r2_hidden(D_104, k4_xboole_0(A_106, B_105)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.31  tff(c_305, plain, (![D_107]: (~r2_hidden(D_107, k1_tarski('#skF_8')) | ~r2_hidden(D_107, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_301])).
% 2.09/1.31  tff(c_309, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_263, c_305])).
% 2.09/1.31  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_309])).
% 2.09/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  Inference rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Ref     : 0
% 2.09/1.31  #Sup     : 55
% 2.09/1.31  #Fact    : 0
% 2.09/1.31  #Define  : 0
% 2.09/1.31  #Split   : 4
% 2.09/1.31  #Chain   : 0
% 2.09/1.31  #Close   : 0
% 2.09/1.31  
% 2.09/1.31  Ordering : KBO
% 2.09/1.31  
% 2.09/1.31  Simplification rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Subsume      : 6
% 2.09/1.31  #Demod        : 10
% 2.09/1.31  #Tautology    : 28
% 2.09/1.31  #SimpNegUnit  : 1
% 2.09/1.31  #BackRed      : 0
% 2.09/1.31  
% 2.09/1.31  #Partial instantiations: 0
% 2.09/1.31  #Strategies tried      : 1
% 2.09/1.31  
% 2.09/1.31  Timing (in seconds)
% 2.09/1.31  ----------------------
% 2.09/1.32  Preprocessing        : 0.32
% 2.09/1.32  Parsing              : 0.16
% 2.09/1.32  CNF conversion       : 0.03
% 2.09/1.32  Main loop            : 0.21
% 2.09/1.32  Inferencing          : 0.07
% 2.09/1.32  Reduction            : 0.06
% 2.37/1.32  Demodulation         : 0.04
% 2.37/1.32  BG Simplification    : 0.02
% 2.37/1.32  Subsumption          : 0.04
% 2.37/1.32  Abstraction          : 0.01
% 2.37/1.32  MUC search           : 0.00
% 2.37/1.32  Cooper               : 0.00
% 2.37/1.32  Total                : 0.56
% 2.37/1.32  Index Insertion      : 0.00
% 2.37/1.32  Index Deletion       : 0.00
% 2.37/1.32  Index Matching       : 0.00
% 2.37/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
