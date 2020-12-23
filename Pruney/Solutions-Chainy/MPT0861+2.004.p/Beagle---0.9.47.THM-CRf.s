%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:01 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   59 ( 105 expanded)
%              Number of equality atoms :   30 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_64,plain,
    ( k1_mcart_1('#skF_5') != '#skF_6'
    | k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_74,plain,(
    k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_123,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(k2_mcart_1(A_57),C_58)
      | ~ r2_hidden(A_57,k2_zfmisc_1(B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_126,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_123])).

tff(c_142,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden(A_63,k4_xboole_0(B_64,k1_tarski(C_65)))
      | C_65 = A_63
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [A_66,C_67,B_68] :
      ( ~ r2_hidden(A_66,k1_tarski(C_67))
      | C_67 = A_66
      | ~ r2_hidden(A_66,B_68) ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_159,plain,(
    ! [B_68] :
      ( k2_mcart_1('#skF_5') = '#skF_8'
      | ~ r2_hidden(k2_mcart_1('#skF_5'),B_68) ) ),
    inference(resolution,[status(thm)],[c_126,c_157])).

tff(c_164,plain,(
    ! [B_68] : ~ r2_hidden(k2_mcart_1('#skF_5'),B_68) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_159])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_126])).

tff(c_169,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_170,plain,(
    k2_mcart_1('#skF_5') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( k1_mcart_1('#skF_5') != '#skF_7'
    | k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    k1_mcart_1('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_62])).

tff(c_221,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k1_mcart_1(A_96),B_97)
      | ~ r2_hidden(A_96,k2_zfmisc_1(B_97,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_224,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_221])).

tff(c_46,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_265,plain,(
    ! [E_111,C_112,B_113,A_114] :
      ( E_111 = C_112
      | E_111 = B_113
      | E_111 = A_114
      | ~ r2_hidden(E_111,k1_enumset1(A_114,B_113,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_284,plain,(
    ! [E_115,B_116,A_117] :
      ( E_115 = B_116
      | E_115 = A_117
      | E_115 = A_117
      | ~ r2_hidden(E_115,k2_tarski(A_117,B_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_265])).

tff(c_287,plain,
    ( k1_mcart_1('#skF_5') = '#skF_7'
    | k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_224,c_284])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_169,c_178,c_287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.09/1.27  
% 2.09/1.27  %Foreground sorts:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Background operators:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Foreground operators:
% 2.09/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.09/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.27  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.09/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.27  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.09/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.09/1.27  
% 2.09/1.28  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.09/1.28  tff(f_69, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.09/1.28  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.09/1.28  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.09/1.28  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.28  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.09/1.28  tff(c_64, plain, (k1_mcart_1('#skF_5')!='#skF_6' | k2_mcart_1('#skF_5')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.28  tff(c_74, plain, (k2_mcart_1('#skF_5')!='#skF_8'), inference(splitLeft, [status(thm)], [c_64])).
% 2.09/1.28  tff(c_60, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.28  tff(c_123, plain, (![A_57, C_58, B_59]: (r2_hidden(k2_mcart_1(A_57), C_58) | ~r2_hidden(A_57, k2_zfmisc_1(B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.09/1.28  tff(c_126, plain, (r2_hidden(k2_mcart_1('#skF_5'), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_123])).
% 2.09/1.28  tff(c_142, plain, (![A_63, B_64, C_65]: (r2_hidden(A_63, k4_xboole_0(B_64, k1_tarski(C_65))) | C_65=A_63 | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.09/1.28  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.28  tff(c_157, plain, (![A_66, C_67, B_68]: (~r2_hidden(A_66, k1_tarski(C_67)) | C_67=A_66 | ~r2_hidden(A_66, B_68))), inference(resolution, [status(thm)], [c_142, c_4])).
% 2.09/1.28  tff(c_159, plain, (![B_68]: (k2_mcart_1('#skF_5')='#skF_8' | ~r2_hidden(k2_mcart_1('#skF_5'), B_68))), inference(resolution, [status(thm)], [c_126, c_157])).
% 2.09/1.28  tff(c_164, plain, (![B_68]: (~r2_hidden(k2_mcart_1('#skF_5'), B_68))), inference(negUnitSimplification, [status(thm)], [c_74, c_159])).
% 2.09/1.28  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_126])).
% 2.09/1.28  tff(c_169, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 2.09/1.28  tff(c_170, plain, (k2_mcart_1('#skF_5')='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 2.09/1.28  tff(c_62, plain, (k1_mcart_1('#skF_5')!='#skF_7' | k2_mcart_1('#skF_5')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.28  tff(c_178, plain, (k1_mcart_1('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_62])).
% 2.09/1.28  tff(c_221, plain, (![A_96, B_97, C_98]: (r2_hidden(k1_mcart_1(A_96), B_97) | ~r2_hidden(A_96, k2_zfmisc_1(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.09/1.28  tff(c_224, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_221])).
% 2.09/1.28  tff(c_46, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.28  tff(c_265, plain, (![E_111, C_112, B_113, A_114]: (E_111=C_112 | E_111=B_113 | E_111=A_114 | ~r2_hidden(E_111, k1_enumset1(A_114, B_113, C_112)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.09/1.28  tff(c_284, plain, (![E_115, B_116, A_117]: (E_115=B_116 | E_115=A_117 | E_115=A_117 | ~r2_hidden(E_115, k2_tarski(A_117, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_265])).
% 2.09/1.28  tff(c_287, plain, (k1_mcart_1('#skF_5')='#skF_7' | k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_224, c_284])).
% 2.09/1.28  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_169, c_178, c_287])).
% 2.09/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  Inference rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Ref     : 0
% 2.09/1.28  #Sup     : 49
% 2.09/1.28  #Fact    : 0
% 2.09/1.28  #Define  : 0
% 2.09/1.28  #Split   : 1
% 2.09/1.28  #Chain   : 0
% 2.09/1.28  #Close   : 0
% 2.09/1.28  
% 2.09/1.28  Ordering : KBO
% 2.09/1.28  
% 2.09/1.28  Simplification rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Subsume      : 2
% 2.09/1.28  #Demod        : 9
% 2.09/1.28  #Tautology    : 32
% 2.09/1.28  #SimpNegUnit  : 3
% 2.09/1.28  #BackRed      : 1
% 2.09/1.28  
% 2.09/1.28  #Partial instantiations: 0
% 2.09/1.28  #Strategies tried      : 1
% 2.09/1.28  
% 2.09/1.28  Timing (in seconds)
% 2.09/1.28  ----------------------
% 2.09/1.28  Preprocessing        : 0.31
% 2.09/1.28  Parsing              : 0.16
% 2.09/1.28  CNF conversion       : 0.02
% 2.09/1.28  Main loop            : 0.21
% 2.09/1.28  Inferencing          : 0.08
% 2.09/1.28  Reduction            : 0.06
% 2.09/1.28  Demodulation         : 0.04
% 2.09/1.28  BG Simplification    : 0.02
% 2.09/1.28  Subsumption          : 0.04
% 2.09/1.28  Abstraction          : 0.01
% 2.09/1.28  MUC search           : 0.00
% 2.09/1.28  Cooper               : 0.00
% 2.09/1.28  Total                : 0.54
% 2.09/1.28  Index Insertion      : 0.00
% 2.09/1.28  Index Deletion       : 0.00
% 2.09/1.28  Index Matching       : 0.00
% 2.09/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
