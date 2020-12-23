%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:49 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   42 (  51 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  77 expanded)
%              Number of equality atoms :   29 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( r2_hidden('#skF_5'(A_19,B_20),A_19)
      | k1_xboole_0 = A_19
      | k1_tarski(B_20) = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k4_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [D_33,A_34] :
      ( ~ r2_hidden(D_33,A_34)
      | ~ r2_hidden(D_33,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_101,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_98])).

tff(c_48,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,(
    ! [D_46,A_47,B_48] :
      ( r2_hidden(D_46,k4_xboole_0(A_47,B_48))
      | r2_hidden(D_46,B_48)
      | ~ r2_hidden(D_46,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152,plain,(
    ! [D_46] :
      ( r2_hidden(D_46,k1_xboole_0)
      | r2_hidden(D_46,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_46,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_143])).

tff(c_160,plain,(
    ! [D_49] :
      ( r2_hidden(D_49,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_49,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_152])).

tff(c_22,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_165,plain,(
    ! [D_50] :
      ( D_50 = '#skF_7'
      | ~ r2_hidden(D_50,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_160,c_22])).

tff(c_169,plain,(
    ! [B_20] :
      ( '#skF_5'('#skF_6',B_20) = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_tarski(B_20) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_42,c_165])).

tff(c_173,plain,(
    ! [B_51] :
      ( '#skF_5'('#skF_6',B_51) = '#skF_7'
      | k1_tarski(B_51) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_169])).

tff(c_196,plain,(
    '#skF_5'('#skF_6','#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_44])).

tff(c_40,plain,(
    ! [A_19,B_20] :
      ( '#skF_5'(A_19,B_20) != B_20
      | k1_xboole_0 = A_19
      | k1_tarski(B_20) = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_203,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_40])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_46,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.19  tff('#skF_7', type, '#skF_7': $i).
% 1.89/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.89/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.89/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.89/1.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.89/1.19  
% 1.89/1.20  tff(f_74, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.89/1.20  tff(f_64, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 1.89/1.20  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.89/1.20  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.89/1.20  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.89/1.20  tff(c_44, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.89/1.20  tff(c_46, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.89/1.20  tff(c_42, plain, (![A_19, B_20]: (r2_hidden('#skF_5'(A_19, B_20), A_19) | k1_xboole_0=A_19 | k1_tarski(B_20)=A_19)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.20  tff(c_24, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.20  tff(c_20, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.20  tff(c_85, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k4_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.20  tff(c_98, plain, (![D_33, A_34]: (~r2_hidden(D_33, A_34) | ~r2_hidden(D_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_85])).
% 1.89/1.20  tff(c_101, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_98])).
% 1.89/1.20  tff(c_48, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.89/1.20  tff(c_143, plain, (![D_46, A_47, B_48]: (r2_hidden(D_46, k4_xboole_0(A_47, B_48)) | r2_hidden(D_46, B_48) | ~r2_hidden(D_46, A_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.20  tff(c_152, plain, (![D_46]: (r2_hidden(D_46, k1_xboole_0) | r2_hidden(D_46, k1_tarski('#skF_7')) | ~r2_hidden(D_46, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_143])).
% 1.89/1.20  tff(c_160, plain, (![D_49]: (r2_hidden(D_49, k1_tarski('#skF_7')) | ~r2_hidden(D_49, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_101, c_152])).
% 1.89/1.20  tff(c_22, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.20  tff(c_165, plain, (![D_50]: (D_50='#skF_7' | ~r2_hidden(D_50, '#skF_6'))), inference(resolution, [status(thm)], [c_160, c_22])).
% 1.89/1.20  tff(c_169, plain, (![B_20]: ('#skF_5'('#skF_6', B_20)='#skF_7' | k1_xboole_0='#skF_6' | k1_tarski(B_20)='#skF_6')), inference(resolution, [status(thm)], [c_42, c_165])).
% 1.89/1.20  tff(c_173, plain, (![B_51]: ('#skF_5'('#skF_6', B_51)='#skF_7' | k1_tarski(B_51)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_169])).
% 1.89/1.20  tff(c_196, plain, ('#skF_5'('#skF_6', '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_173, c_44])).
% 1.89/1.20  tff(c_40, plain, (![A_19, B_20]: ('#skF_5'(A_19, B_20)!=B_20 | k1_xboole_0=A_19 | k1_tarski(B_20)=A_19)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.20  tff(c_203, plain, (k1_xboole_0='#skF_6' | k1_tarski('#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_196, c_40])).
% 1.89/1.20  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_46, c_203])).
% 1.89/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  Inference rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Ref     : 0
% 1.89/1.20  #Sup     : 38
% 1.89/1.20  #Fact    : 0
% 1.89/1.20  #Define  : 0
% 1.89/1.20  #Split   : 0
% 1.89/1.20  #Chain   : 0
% 1.89/1.20  #Close   : 0
% 1.89/1.20  
% 1.89/1.20  Ordering : KBO
% 1.89/1.20  
% 1.89/1.20  Simplification rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Subsume      : 6
% 1.89/1.20  #Demod        : 0
% 1.89/1.20  #Tautology    : 18
% 1.89/1.20  #SimpNegUnit  : 6
% 1.89/1.20  #BackRed      : 0
% 1.89/1.20  
% 1.89/1.20  #Partial instantiations: 0
% 1.89/1.20  #Strategies tried      : 1
% 1.89/1.20  
% 1.89/1.20  Timing (in seconds)
% 1.89/1.20  ----------------------
% 1.89/1.21  Preprocessing        : 0.30
% 1.89/1.21  Parsing              : 0.15
% 1.89/1.21  CNF conversion       : 0.02
% 1.89/1.21  Main loop            : 0.15
% 1.89/1.21  Inferencing          : 0.05
% 1.89/1.21  Reduction            : 0.05
% 1.89/1.21  Demodulation         : 0.03
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.03
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.48
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
