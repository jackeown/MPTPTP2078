%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:35 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   60 (  86 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 125 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_38,plain,
    ( k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2'
    | r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_107,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [B_33] : k4_xboole_0(B_33,B_33) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_34,plain,(
    ! [C_24,B_23] : ~ r2_hidden(C_24,k4_xboole_0(B_23,k1_tarski(C_24))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_101,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_34])).

tff(c_95,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_323,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden(A_73,k4_xboole_0(B_74,k1_tarski(C_75)))
      | C_75 = A_73
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_340,plain,(
    ! [A_73,C_75] :
      ( r2_hidden(A_73,k1_xboole_0)
      | C_75 = A_73
      | ~ r2_hidden(A_73,k1_tarski(C_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_323])).

tff(c_347,plain,(
    ! [C_76,A_77] :
      ( C_76 = A_77
      | ~ r2_hidden(A_77,k1_tarski(C_76)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_340])).

tff(c_397,plain,(
    ! [A_83,C_84] :
      ( '#skF_1'(A_83,k1_tarski(C_84)) = C_84
      | r1_xboole_0(A_83,k1_tarski(C_84)) ) ),
    inference(resolution,[status(thm)],[c_6,c_347])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_406,plain,(
    ! [A_85,C_86] :
      ( k4_xboole_0(A_85,k1_tarski(C_86)) = A_85
      | '#skF_1'(A_85,k1_tarski(C_86)) = C_86 ) ),
    inference(resolution,[status(thm)],[c_397,c_22])).

tff(c_448,plain,(
    '#skF_1'('#skF_2',k1_tarski('#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_107])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_454,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | r1_xboole_0('#skF_2',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_8])).

tff(c_460,plain,(
    r1_xboole_0('#skF_2',k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_454])).

tff(c_466,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_460,c_22])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_466])).

tff(c_472,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_473,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2'
    | k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_633,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_42])).

tff(c_637,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_34])).

tff(c_642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_637])).

tff(c_643,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_644,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_783,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_44])).

tff(c_787,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_34])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:55:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  
% 2.57/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.57/1.37  
% 2.57/1.37  %Foreground sorts:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Background operators:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Foreground operators:
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.37  
% 2.81/1.38  tff(f_80, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.81/1.38  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.81/1.38  tff(f_51, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.38  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.81/1.38  tff(f_74, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.81/1.38  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.81/1.38  tff(c_38, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2' | r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.81/1.38  tff(c_107, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 2.81/1.38  tff(c_40, plain, (~r2_hidden('#skF_3', '#skF_2') | r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.81/1.38  tff(c_56, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.81/1.38  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.38  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.38  tff(c_91, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.81/1.38  tff(c_96, plain, (![B_33]: (k4_xboole_0(B_33, B_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_91])).
% 2.81/1.38  tff(c_34, plain, (![C_24, B_23]: (~r2_hidden(C_24, k4_xboole_0(B_23, k1_tarski(C_24))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.81/1.38  tff(c_101, plain, (![C_24]: (~r2_hidden(C_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_96, c_34])).
% 2.81/1.38  tff(c_95, plain, (![B_9]: (k4_xboole_0(B_9, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_91])).
% 2.81/1.38  tff(c_323, plain, (![A_73, B_74, C_75]: (r2_hidden(A_73, k4_xboole_0(B_74, k1_tarski(C_75))) | C_75=A_73 | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.81/1.38  tff(c_340, plain, (![A_73, C_75]: (r2_hidden(A_73, k1_xboole_0) | C_75=A_73 | ~r2_hidden(A_73, k1_tarski(C_75)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_323])).
% 2.81/1.38  tff(c_347, plain, (![C_76, A_77]: (C_76=A_77 | ~r2_hidden(A_77, k1_tarski(C_76)))), inference(negUnitSimplification, [status(thm)], [c_101, c_340])).
% 2.81/1.38  tff(c_397, plain, (![A_83, C_84]: ('#skF_1'(A_83, k1_tarski(C_84))=C_84 | r1_xboole_0(A_83, k1_tarski(C_84)))), inference(resolution, [status(thm)], [c_6, c_347])).
% 2.81/1.38  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.38  tff(c_406, plain, (![A_85, C_86]: (k4_xboole_0(A_85, k1_tarski(C_86))=A_85 | '#skF_1'(A_85, k1_tarski(C_86))=C_86)), inference(resolution, [status(thm)], [c_397, c_22])).
% 2.81/1.38  tff(c_448, plain, ('#skF_1'('#skF_2', k1_tarski('#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_406, c_107])).
% 2.81/1.38  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.38  tff(c_454, plain, (r2_hidden('#skF_3', '#skF_2') | r1_xboole_0('#skF_2', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_448, c_8])).
% 2.81/1.38  tff(c_460, plain, (r1_xboole_0('#skF_2', k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_454])).
% 2.81/1.38  tff(c_466, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_460, c_22])).
% 2.81/1.38  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_466])).
% 2.81/1.38  tff(c_472, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 2.81/1.38  tff(c_473, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 2.81/1.38  tff(c_42, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2' | k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.81/1.38  tff(c_633, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_42])).
% 2.81/1.38  tff(c_637, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_633, c_34])).
% 2.81/1.38  tff(c_642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_472, c_637])).
% 2.81/1.38  tff(c_643, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.81/1.38  tff(c_644, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.81/1.38  tff(c_44, plain, (~r2_hidden('#skF_3', '#skF_2') | k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.81/1.38  tff(c_783, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_644, c_44])).
% 2.81/1.38  tff(c_787, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_783, c_34])).
% 2.81/1.38  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_643, c_787])).
% 2.81/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  Inference rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Ref     : 0
% 2.81/1.38  #Sup     : 168
% 2.81/1.38  #Fact    : 0
% 2.81/1.38  #Define  : 0
% 2.81/1.38  #Split   : 2
% 2.81/1.38  #Chain   : 0
% 2.81/1.38  #Close   : 0
% 2.81/1.38  
% 2.81/1.38  Ordering : KBO
% 2.81/1.38  
% 2.81/1.38  Simplification rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Subsume      : 11
% 2.81/1.38  #Demod        : 33
% 2.81/1.38  #Tautology    : 108
% 2.81/1.38  #SimpNegUnit  : 6
% 2.81/1.38  #BackRed      : 0
% 2.81/1.38  
% 2.81/1.38  #Partial instantiations: 0
% 2.81/1.38  #Strategies tried      : 1
% 2.81/1.38  
% 2.81/1.38  Timing (in seconds)
% 2.81/1.38  ----------------------
% 2.81/1.38  Preprocessing        : 0.32
% 2.81/1.38  Parsing              : 0.16
% 2.81/1.38  CNF conversion       : 0.02
% 2.81/1.38  Main loop            : 0.31
% 2.81/1.38  Inferencing          : 0.12
% 2.81/1.38  Reduction            : 0.09
% 2.81/1.38  Demodulation         : 0.06
% 2.81/1.38  BG Simplification    : 0.02
% 2.81/1.38  Subsumption          : 0.05
% 2.81/1.38  Abstraction          : 0.02
% 2.81/1.38  MUC search           : 0.00
% 2.81/1.38  Cooper               : 0.00
% 2.81/1.39  Total                : 0.66
% 2.81/1.39  Index Insertion      : 0.00
% 2.81/1.39  Index Deletion       : 0.00
% 2.81/1.39  Index Matching       : 0.00
% 2.81/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
