%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:35 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  98 expanded)
%              Number of equality atoms :   31 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_108,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,B_62)
      | ~ r2_hidden(C_63,A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_56,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_123,plain,(
    ! [B_65,A_66] :
      ( k1_tarski(B_65) = A_66
      | k1_xboole_0 = A_66
      | ~ r1_tarski(A_66,k1_tarski(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_135,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_123])).

tff(c_159,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_36,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_77,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [E_13,B_8,C_9] : r2_hidden(E_13,k1_enumset1(E_13,B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_95,plain,(
    ! [A_52,B_53] : r2_hidden(A_52,k2_tarski(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_18])).

tff(c_98,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_95])).

tff(c_168,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_98])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_168])).

tff(c_182,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_201,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_98])).

tff(c_38,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_226,plain,(
    ! [E_76,C_77,B_78,A_79] :
      ( E_76 = C_77
      | E_76 = B_78
      | E_76 = A_79
      | ~ r2_hidden(E_76,k1_enumset1(A_79,B_78,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_255,plain,(
    ! [E_80,B_81,A_82] :
      ( E_80 = B_81
      | E_80 = A_82
      | E_80 = A_82
      | ~ r2_hidden(E_80,k2_tarski(A_82,B_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_226])).

tff(c_279,plain,(
    ! [E_83,A_84] :
      ( E_83 = A_84
      | E_83 = A_84
      | E_83 = A_84
      | ~ r2_hidden(E_83,k1_tarski(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_255])).

tff(c_282,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_201,c_279])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.43  
% 2.39/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.39/1.44  
% 2.39/1.44  %Foreground sorts:
% 2.39/1.44  
% 2.39/1.44  
% 2.39/1.44  %Background operators:
% 2.39/1.44  
% 2.39/1.44  
% 2.39/1.44  %Foreground operators:
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.39/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.39/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.39/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.39/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.39/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.44  
% 2.39/1.45  tff(f_93, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.39/1.45  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.39/1.45  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.39/1.45  tff(f_88, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.39/1.45  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.39/1.45  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.39/1.45  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.39/1.45  tff(c_54, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.39/1.45  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.39/1.45  tff(c_108, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, B_62) | ~r2_hidden(C_63, A_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.45  tff(c_111, plain, (![C_63]: (~r2_hidden(C_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_108])).
% 2.39/1.45  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.39/1.45  tff(c_123, plain, (![B_65, A_66]: (k1_tarski(B_65)=A_66 | k1_xboole_0=A_66 | ~r1_tarski(A_66, k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.39/1.45  tff(c_135, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_123])).
% 2.39/1.45  tff(c_159, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_135])).
% 2.39/1.45  tff(c_36, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.39/1.45  tff(c_77, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.39/1.45  tff(c_18, plain, (![E_13, B_8, C_9]: (r2_hidden(E_13, k1_enumset1(E_13, B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.39/1.45  tff(c_95, plain, (![A_52, B_53]: (r2_hidden(A_52, k2_tarski(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_18])).
% 2.39/1.45  tff(c_98, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_95])).
% 2.39/1.45  tff(c_168, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_98])).
% 2.39/1.45  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_168])).
% 2.39/1.45  tff(c_182, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_135])).
% 2.39/1.45  tff(c_201, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_98])).
% 2.39/1.45  tff(c_38, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.39/1.45  tff(c_226, plain, (![E_76, C_77, B_78, A_79]: (E_76=C_77 | E_76=B_78 | E_76=A_79 | ~r2_hidden(E_76, k1_enumset1(A_79, B_78, C_77)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.39/1.45  tff(c_255, plain, (![E_80, B_81, A_82]: (E_80=B_81 | E_80=A_82 | E_80=A_82 | ~r2_hidden(E_80, k2_tarski(A_82, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_226])).
% 2.39/1.45  tff(c_279, plain, (![E_83, A_84]: (E_83=A_84 | E_83=A_84 | E_83=A_84 | ~r2_hidden(E_83, k1_tarski(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_255])).
% 2.39/1.45  tff(c_282, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_201, c_279])).
% 2.39/1.45  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_282])).
% 2.39/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.45  
% 2.39/1.45  Inference rules
% 2.39/1.45  ----------------------
% 2.39/1.45  #Ref     : 0
% 2.39/1.45  #Sup     : 54
% 2.39/1.45  #Fact    : 0
% 2.39/1.45  #Define  : 0
% 2.39/1.45  #Split   : 1
% 2.39/1.45  #Chain   : 0
% 2.39/1.45  #Close   : 0
% 2.39/1.45  
% 2.39/1.45  Ordering : KBO
% 2.39/1.45  
% 2.39/1.45  Simplification rules
% 2.39/1.45  ----------------------
% 2.39/1.45  #Subsume      : 3
% 2.39/1.45  #Demod        : 14
% 2.39/1.45  #Tautology    : 29
% 2.39/1.45  #SimpNegUnit  : 2
% 2.39/1.45  #BackRed      : 2
% 2.39/1.45  
% 2.39/1.45  #Partial instantiations: 0
% 2.39/1.45  #Strategies tried      : 1
% 2.39/1.45  
% 2.39/1.45  Timing (in seconds)
% 2.39/1.45  ----------------------
% 2.39/1.45  Preprocessing        : 0.38
% 2.39/1.45  Parsing              : 0.20
% 2.39/1.45  CNF conversion       : 0.03
% 2.39/1.45  Main loop            : 0.21
% 2.39/1.45  Inferencing          : 0.08
% 2.39/1.45  Reduction            : 0.07
% 2.39/1.45  Demodulation         : 0.05
% 2.39/1.45  BG Simplification    : 0.02
% 2.39/1.45  Subsumption          : 0.04
% 2.39/1.45  Abstraction          : 0.01
% 2.39/1.45  MUC search           : 0.00
% 2.39/1.45  Cooper               : 0.00
% 2.39/1.45  Total                : 0.63
% 2.39/1.45  Index Insertion      : 0.00
% 2.39/1.45  Index Deletion       : 0.00
% 2.39/1.45  Index Matching       : 0.00
% 2.39/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
