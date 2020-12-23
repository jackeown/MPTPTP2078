%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:33 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   54 (  87 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 ( 107 expanded)
%              Number of equality atoms :   26 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_72,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_74,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_239,plain,(
    ! [B_66,A_67] :
      ( k1_tarski(B_66) = A_67
      | k1_xboole_0 = A_67
      | ~ r1_tarski(A_67,k1_tarski(B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_256,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_239])).

tff(c_265,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_48,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_283,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_48])).

tff(c_16,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ r1_tarski(A_40,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    ! [B_7] : k3_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_88])).

tff(c_156,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_168,plain,(
    ! [B_62] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_156])).

tff(c_165,plain,(
    ! [B_7] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_156])).

tff(c_177,plain,(
    ! [B_64,B_63] : k4_xboole_0(k1_xboole_0,B_64) = k4_xboole_0(k1_xboole_0,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_165])).

tff(c_18,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_193,plain,(
    ! [B_64] : k4_xboole_0(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_18])).

tff(c_219,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_165])).

tff(c_346,plain,(
    ! [A_85,C_86,B_87] :
      ( ~ r2_hidden(A_85,C_86)
      | ~ r2_hidden(A_85,B_87)
      | ~ r2_hidden(A_85,k5_xboole_0(B_87,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_708,plain,(
    ! [A_1192] :
      ( ~ r2_hidden(A_1192,k1_xboole_0)
      | ~ r2_hidden(A_1192,k1_xboole_0)
      | ~ r2_hidden(A_1192,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_346])).

tff(c_710,plain,(
    ~ r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_283,c_708])).

tff(c_714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_710])).

tff(c_715,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_735,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_48])).

tff(c_46,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_747,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_735,c_46])).

tff(c_751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.43  
% 2.36/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.43  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.36/1.43  
% 2.36/1.43  %Foreground sorts:
% 2.36/1.43  
% 2.36/1.43  
% 2.36/1.43  %Background operators:
% 2.36/1.43  
% 2.36/1.43  
% 2.36/1.43  %Foreground operators:
% 2.36/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.36/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.36/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.36/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.36/1.43  
% 2.64/1.44  tff(f_83, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.64/1.44  tff(f_78, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.64/1.44  tff(f_64, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.64/1.44  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.64/1.44  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.64/1.44  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.64/1.44  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.64/1.44  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.64/1.44  tff(c_72, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.64/1.44  tff(c_74, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.64/1.44  tff(c_239, plain, (![B_66, A_67]: (k1_tarski(B_66)=A_67 | k1_xboole_0=A_67 | ~r1_tarski(A_67, k1_tarski(B_66)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.44  tff(c_256, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_239])).
% 2.64/1.44  tff(c_265, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_256])).
% 2.64/1.44  tff(c_48, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.44  tff(c_283, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_265, c_48])).
% 2.64/1.44  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.64/1.44  tff(c_88, plain, (![A_40]: (k1_xboole_0=A_40 | ~r1_tarski(A_40, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.64/1.44  tff(c_93, plain, (![B_7]: (k3_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_88])).
% 2.64/1.44  tff(c_156, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.64/1.44  tff(c_168, plain, (![B_62]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_62))), inference(superposition, [status(thm), theory('equality')], [c_93, c_156])).
% 2.64/1.44  tff(c_165, plain, (![B_7]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_7))), inference(superposition, [status(thm), theory('equality')], [c_93, c_156])).
% 2.64/1.44  tff(c_177, plain, (![B_64, B_63]: (k4_xboole_0(k1_xboole_0, B_64)=k4_xboole_0(k1_xboole_0, B_63))), inference(superposition, [status(thm), theory('equality')], [c_168, c_165])).
% 2.64/1.44  tff(c_18, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.64/1.44  tff(c_193, plain, (![B_64]: (k4_xboole_0(k1_xboole_0, B_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_177, c_18])).
% 2.64/1.44  tff(c_219, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_193, c_165])).
% 2.64/1.44  tff(c_346, plain, (![A_85, C_86, B_87]: (~r2_hidden(A_85, C_86) | ~r2_hidden(A_85, B_87) | ~r2_hidden(A_85, k5_xboole_0(B_87, C_86)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.44  tff(c_708, plain, (![A_1192]: (~r2_hidden(A_1192, k1_xboole_0) | ~r2_hidden(A_1192, k1_xboole_0) | ~r2_hidden(A_1192, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_219, c_346])).
% 2.64/1.44  tff(c_710, plain, (~r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_283, c_708])).
% 2.64/1.44  tff(c_714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_710])).
% 2.64/1.44  tff(c_715, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_256])).
% 2.64/1.44  tff(c_735, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_715, c_48])).
% 2.64/1.44  tff(c_46, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.44  tff(c_747, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_735, c_46])).
% 2.64/1.44  tff(c_751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_747])).
% 2.64/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.44  
% 2.64/1.44  Inference rules
% 2.64/1.44  ----------------------
% 2.64/1.44  #Ref     : 0
% 2.64/1.44  #Sup     : 111
% 2.64/1.44  #Fact    : 0
% 2.64/1.44  #Define  : 0
% 2.64/1.44  #Split   : 1
% 2.64/1.44  #Chain   : 0
% 2.64/1.44  #Close   : 0
% 2.64/1.44  
% 2.64/1.44  Ordering : KBO
% 2.64/1.44  
% 2.64/1.44  Simplification rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Subsume      : 14
% 2.64/1.45  #Demod        : 30
% 2.64/1.45  #Tautology    : 61
% 2.64/1.45  #SimpNegUnit  : 1
% 2.64/1.45  #BackRed      : 4
% 2.64/1.45  
% 2.64/1.45  #Partial instantiations: 495
% 2.64/1.45  #Strategies tried      : 1
% 2.64/1.45  
% 2.64/1.45  Timing (in seconds)
% 2.64/1.45  ----------------------
% 2.64/1.45  Preprocessing        : 0.33
% 2.64/1.45  Parsing              : 0.17
% 2.64/1.45  CNF conversion       : 0.03
% 2.64/1.45  Main loop            : 0.29
% 2.64/1.45  Inferencing          : 0.14
% 2.64/1.45  Reduction            : 0.08
% 2.64/1.45  Demodulation         : 0.06
% 2.64/1.45  BG Simplification    : 0.02
% 2.64/1.45  Subsumption          : 0.04
% 2.64/1.45  Abstraction          : 0.01
% 2.64/1.45  MUC search           : 0.00
% 2.64/1.45  Cooper               : 0.00
% 2.64/1.45  Total                : 0.65
% 2.64/1.45  Index Insertion      : 0.00
% 2.64/1.45  Index Deletion       : 0.00
% 2.64/1.45  Index Matching       : 0.00
% 2.64/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
