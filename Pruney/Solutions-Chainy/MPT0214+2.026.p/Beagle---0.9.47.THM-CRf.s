%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:33 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   47 (  65 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  82 expanded)
%              Number of equality atoms :   21 (  43 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_68,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_70,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_160,plain,(
    ! [B_55,A_56] :
      ( k1_tarski(B_55) = A_56
      | k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,k1_tarski(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_172,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_160])).

tff(c_175,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_46,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_193,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_46])).

tff(c_18,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_134,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_143,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_134])).

tff(c_224,plain,(
    ! [A_62,C_63,B_64] :
      ( ~ r2_hidden(A_62,C_63)
      | ~ r2_hidden(A_62,B_64)
      | ~ r2_hidden(A_62,k5_xboole_0(B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_740,plain,(
    ! [A_1218,A_1219] :
      ( ~ r2_hidden(A_1218,A_1219)
      | ~ r2_hidden(A_1218,A_1219)
      | ~ r2_hidden(A_1218,k4_xboole_0(A_1219,A_1219)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_224])).

tff(c_751,plain,(
    ! [A_1248] :
      ( ~ r2_hidden(A_1248,k1_xboole_0)
      | ~ r2_hidden(A_1248,k1_xboole_0)
      | ~ r2_hidden(A_1248,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_740])).

tff(c_758,plain,(
    ~ r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_193,c_751])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_758])).

tff(c_765,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_785,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_46])).

tff(c_44,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_797,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_785,c_44])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_797])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.44  
% 2.47/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.44  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.47/1.44  
% 2.47/1.44  %Foreground sorts:
% 2.47/1.44  
% 2.47/1.44  
% 2.47/1.44  %Background operators:
% 2.47/1.44  
% 2.47/1.44  
% 2.47/1.44  %Foreground operators:
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.47/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.47/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.47/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.47/1.44  
% 2.86/1.45  tff(f_77, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.86/1.45  tff(f_72, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.86/1.45  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.86/1.45  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.86/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.86/1.45  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.86/1.45  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.86/1.45  tff(c_68, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.45  tff(c_70, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.45  tff(c_160, plain, (![B_55, A_56]: (k1_tarski(B_55)=A_56 | k1_xboole_0=A_56 | ~r1_tarski(A_56, k1_tarski(B_55)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.45  tff(c_172, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_160])).
% 2.86/1.45  tff(c_175, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_172])).
% 2.86/1.45  tff(c_46, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.45  tff(c_193, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_175, c_46])).
% 2.86/1.45  tff(c_18, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.45  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.45  tff(c_134, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.86/1.45  tff(c_143, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_134])).
% 2.86/1.45  tff(c_224, plain, (![A_62, C_63, B_64]: (~r2_hidden(A_62, C_63) | ~r2_hidden(A_62, B_64) | ~r2_hidden(A_62, k5_xboole_0(B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.86/1.45  tff(c_740, plain, (![A_1218, A_1219]: (~r2_hidden(A_1218, A_1219) | ~r2_hidden(A_1218, A_1219) | ~r2_hidden(A_1218, k4_xboole_0(A_1219, A_1219)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_224])).
% 2.86/1.45  tff(c_751, plain, (![A_1248]: (~r2_hidden(A_1248, k1_xboole_0) | ~r2_hidden(A_1248, k1_xboole_0) | ~r2_hidden(A_1248, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_740])).
% 2.86/1.45  tff(c_758, plain, (~r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_193, c_751])).
% 2.86/1.45  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_758])).
% 2.86/1.45  tff(c_765, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_172])).
% 2.86/1.45  tff(c_785, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_765, c_46])).
% 2.86/1.45  tff(c_44, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.45  tff(c_797, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_785, c_44])).
% 2.86/1.45  tff(c_801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_797])).
% 2.86/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  Inference rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Ref     : 0
% 2.86/1.45  #Sup     : 107
% 2.86/1.45  #Fact    : 0
% 2.86/1.45  #Define  : 0
% 2.86/1.45  #Split   : 4
% 2.86/1.45  #Chain   : 0
% 2.86/1.45  #Close   : 0
% 2.86/1.45  
% 2.86/1.45  Ordering : KBO
% 2.86/1.45  
% 2.86/1.45  Simplification rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Subsume      : 3
% 2.86/1.45  #Demod        : 24
% 2.86/1.45  #Tautology    : 54
% 2.86/1.45  #SimpNegUnit  : 1
% 2.86/1.45  #BackRed      : 3
% 2.86/1.45  
% 2.86/1.45  #Partial instantiations: 574
% 2.86/1.45  #Strategies tried      : 1
% 2.86/1.45  
% 2.86/1.45  Timing (in seconds)
% 2.86/1.45  ----------------------
% 2.86/1.46  Preprocessing        : 0.34
% 2.86/1.46  Parsing              : 0.17
% 2.86/1.46  CNF conversion       : 0.03
% 2.86/1.46  Main loop            : 0.33
% 2.86/1.46  Inferencing          : 0.15
% 2.86/1.46  Reduction            : 0.08
% 2.86/1.46  Demodulation         : 0.06
% 2.86/1.46  BG Simplification    : 0.02
% 2.86/1.46  Subsumption          : 0.05
% 2.86/1.46  Abstraction          : 0.02
% 2.86/1.46  MUC search           : 0.00
% 2.86/1.46  Cooper               : 0.00
% 2.86/1.46  Total                : 0.70
% 2.86/1.46  Index Insertion      : 0.00
% 2.86/1.46  Index Deletion       : 0.00
% 2.86/1.46  Index Matching       : 0.00
% 2.86/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
