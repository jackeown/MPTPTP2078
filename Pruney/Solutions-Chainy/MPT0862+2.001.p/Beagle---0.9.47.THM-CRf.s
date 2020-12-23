%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:04 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    5
%              Number of atoms          :   59 ( 112 expanded)
%              Number of equality atoms :   30 (  64 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_73,axiom,(
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
    ( k2_mcart_1('#skF_5') != '#skF_8'
    | k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_76,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k1_tarski('#skF_6'),k2_tarski('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_125,plain,(
    ! [A_60,B_61,C_62] :
      ( r2_hidden(k1_mcart_1(A_60),B_61)
      | ~ r2_hidden(A_60,k2_zfmisc_1(B_61,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_128,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_62,c_125])).

tff(c_144,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden(A_66,k4_xboole_0(B_67,k1_tarski(C_68)))
      | C_68 = A_66
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_159,plain,(
    ! [A_69,C_70,B_71] :
      ( ~ r2_hidden(A_69,k1_tarski(C_70))
      | C_70 = A_69
      | ~ r2_hidden(A_69,B_71) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_161,plain,(
    ! [B_71] :
      ( k1_mcart_1('#skF_5') = '#skF_6'
      | ~ r2_hidden(k1_mcart_1('#skF_5'),B_71) ) ),
    inference(resolution,[status(thm)],[c_128,c_159])).

tff(c_166,plain,(
    ! [B_71] : ~ r2_hidden(k1_mcart_1('#skF_5'),B_71) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_161])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_128])).

tff(c_172,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_66,plain,
    ( k2_mcart_1('#skF_5') != '#skF_7'
    | k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_179,plain,(
    k2_mcart_1('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_66])).

tff(c_171,plain,(
    k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_223,plain,(
    ! [A_99,C_100,B_101] :
      ( r2_hidden(k2_mcart_1(A_99),C_100)
      | ~ r2_hidden(A_99,k2_zfmisc_1(B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_226,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_62,c_223])).

tff(c_46,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_267,plain,(
    ! [E_114,C_115,B_116,A_117] :
      ( E_114 = C_115
      | E_114 = B_116
      | E_114 = A_117
      | ~ r2_hidden(E_114,k1_enumset1(A_117,B_116,C_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_286,plain,(
    ! [E_118,B_119,A_120] :
      ( E_118 = B_119
      | E_118 = A_120
      | E_118 = A_120
      | ~ r2_hidden(E_118,k2_tarski(A_120,B_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_267])).

tff(c_289,plain,
    ( k2_mcart_1('#skF_5') = '#skF_8'
    | k2_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_226,c_286])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_179,c_171,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.28  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.24/1.28  
% 2.24/1.28  %Foreground sorts:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Background operators:
% 2.24/1.28  
% 2.24/1.28  
% 2.24/1.28  %Foreground operators:
% 2.24/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.24/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.24/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.24/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.28  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.24/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.28  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.24/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.24/1.28  
% 2.24/1.29  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.24/1.29  tff(f_79, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.24/1.29  tff(f_73, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.24/1.29  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.24/1.29  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.29  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.24/1.29  tff(c_64, plain, (k2_mcart_1('#skF_5')!='#skF_8' | k1_mcart_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.24/1.29  tff(c_76, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_64])).
% 2.24/1.29  tff(c_62, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k1_tarski('#skF_6'), k2_tarski('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.24/1.29  tff(c_125, plain, (![A_60, B_61, C_62]: (r2_hidden(k1_mcart_1(A_60), B_61) | ~r2_hidden(A_60, k2_zfmisc_1(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.24/1.29  tff(c_128, plain, (r2_hidden(k1_mcart_1('#skF_5'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_125])).
% 2.24/1.29  tff(c_144, plain, (![A_66, B_67, C_68]: (r2_hidden(A_66, k4_xboole_0(B_67, k1_tarski(C_68))) | C_68=A_66 | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.24/1.29  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.29  tff(c_159, plain, (![A_69, C_70, B_71]: (~r2_hidden(A_69, k1_tarski(C_70)) | C_70=A_69 | ~r2_hidden(A_69, B_71))), inference(resolution, [status(thm)], [c_144, c_4])).
% 2.24/1.29  tff(c_161, plain, (![B_71]: (k1_mcart_1('#skF_5')='#skF_6' | ~r2_hidden(k1_mcart_1('#skF_5'), B_71))), inference(resolution, [status(thm)], [c_128, c_159])).
% 2.24/1.29  tff(c_166, plain, (![B_71]: (~r2_hidden(k1_mcart_1('#skF_5'), B_71))), inference(negUnitSimplification, [status(thm)], [c_76, c_161])).
% 2.24/1.29  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_128])).
% 2.24/1.29  tff(c_172, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 2.24/1.29  tff(c_66, plain, (k2_mcart_1('#skF_5')!='#skF_7' | k1_mcart_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.24/1.29  tff(c_179, plain, (k2_mcart_1('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_66])).
% 2.24/1.29  tff(c_171, plain, (k2_mcart_1('#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 2.24/1.29  tff(c_223, plain, (![A_99, C_100, B_101]: (r2_hidden(k2_mcart_1(A_99), C_100) | ~r2_hidden(A_99, k2_zfmisc_1(B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.24/1.29  tff(c_226, plain, (r2_hidden(k2_mcart_1('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_62, c_223])).
% 2.24/1.29  tff(c_46, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.24/1.29  tff(c_267, plain, (![E_114, C_115, B_116, A_117]: (E_114=C_115 | E_114=B_116 | E_114=A_117 | ~r2_hidden(E_114, k1_enumset1(A_117, B_116, C_115)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.29  tff(c_286, plain, (![E_118, B_119, A_120]: (E_118=B_119 | E_118=A_120 | E_118=A_120 | ~r2_hidden(E_118, k2_tarski(A_120, B_119)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_267])).
% 2.24/1.29  tff(c_289, plain, (k2_mcart_1('#skF_5')='#skF_8' | k2_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_226, c_286])).
% 2.24/1.29  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_179, c_171, c_289])).
% 2.24/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.29  
% 2.24/1.29  Inference rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Ref     : 0
% 2.24/1.29  #Sup     : 49
% 2.24/1.29  #Fact    : 0
% 2.24/1.29  #Define  : 0
% 2.24/1.29  #Split   : 1
% 2.24/1.29  #Chain   : 0
% 2.24/1.29  #Close   : 0
% 2.24/1.29  
% 2.24/1.29  Ordering : KBO
% 2.24/1.29  
% 2.24/1.29  Simplification rules
% 2.24/1.29  ----------------------
% 2.24/1.29  #Subsume      : 2
% 2.24/1.29  #Demod        : 9
% 2.24/1.29  #Tautology    : 32
% 2.24/1.29  #SimpNegUnit  : 3
% 2.24/1.29  #BackRed      : 1
% 2.24/1.29  
% 2.24/1.29  #Partial instantiations: 0
% 2.24/1.29  #Strategies tried      : 1
% 2.24/1.29  
% 2.24/1.29  Timing (in seconds)
% 2.24/1.29  ----------------------
% 2.24/1.30  Preprocessing        : 0.32
% 2.24/1.30  Parsing              : 0.16
% 2.24/1.30  CNF conversion       : 0.03
% 2.24/1.30  Main loop            : 0.22
% 2.24/1.30  Inferencing          : 0.08
% 2.24/1.30  Reduction            : 0.07
% 2.24/1.30  Demodulation         : 0.05
% 2.24/1.30  BG Simplification    : 0.02
% 2.24/1.30  Subsumption          : 0.04
% 2.24/1.30  Abstraction          : 0.01
% 2.24/1.30  MUC search           : 0.00
% 2.24/1.30  Cooper               : 0.00
% 2.24/1.30  Total                : 0.57
% 2.24/1.30  Index Insertion      : 0.00
% 2.24/1.30  Index Deletion       : 0.00
% 2.24/1.30  Index Matching       : 0.00
% 2.24/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
