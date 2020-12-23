%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:23 EST 2020

% Result     : Theorem 11.67s
% Output     : CNFRefutation 11.79s
% Verified   : 
% Statistics : Number of formulae       :   52 (  92 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 ( 118 expanded)
%              Number of equality atoms :   33 (  81 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( k3_xboole_0(B_26,k1_tarski(A_25)) = k1_tarski(A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [C_29,B_28] : r1_tarski(k1_tarski(C_29),k2_tarski(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_126,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_142,plain,(
    ! [C_29,B_28] : k3_xboole_0(k1_tarski(C_29),k2_tarski(B_28,C_29)) = k1_tarski(C_29) ),
    inference(resolution,[status(thm)],[c_36,c_126])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_317,plain,(
    ! [A_67,B_68,C_69] : k3_xboole_0(k3_xboole_0(A_67,B_68),C_69) = k3_xboole_0(A_67,k3_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1689,plain,(
    ! [B_121,A_122,B_123] : k3_xboole_0(B_121,k3_xboole_0(A_122,B_123)) = k3_xboole_0(A_122,k3_xboole_0(B_123,B_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_317])).

tff(c_46,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_385,plain,(
    ! [C_69] : k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k3_xboole_0('#skF_5',C_69)) = k3_xboole_0(k1_tarski('#skF_3'),C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_317])).

tff(c_4415,plain,(
    ! [B_150] : k3_xboole_0('#skF_5',k3_xboole_0(B_150,k2_tarski('#skF_3','#skF_4'))) = k3_xboole_0(k1_tarski('#skF_3'),B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_1689,c_385])).

tff(c_4509,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k3_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_4415])).

tff(c_4581,plain,
    ( k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4509,c_30])).

tff(c_18422,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4581])).

tff(c_2413,plain,(
    ! [A_125] : k3_xboole_0('#skF_5',k3_xboole_0(A_125,k2_tarski('#skF_3','#skF_4'))) = k3_xboole_0(A_125,k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1689])).

tff(c_2483,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_2413])).

tff(c_247,plain,(
    ! [B_61,A_62] :
      ( r2_hidden(B_61,A_62)
      | k3_xboole_0(A_62,k1_tarski(B_61)) != k1_tarski(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_261,plain,(
    ! [B_61,B_2] :
      ( r2_hidden(B_61,B_2)
      | k3_xboole_0(k1_tarski(B_61),B_2) != k1_tarski(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_247])).

tff(c_3474,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_3'))
    | k3_xboole_0('#skF_5',k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2483,c_261])).

tff(c_21168,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_18422,c_3474])).

tff(c_21171,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_21168])).

tff(c_21175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_21171])).

tff(c_21177,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4581])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_21190,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21177,c_8])).

tff(c_21202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_21190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:52:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.67/5.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.67/5.36  
% 11.67/5.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.67/5.37  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.67/5.37  
% 11.67/5.37  %Foreground sorts:
% 11.67/5.37  
% 11.67/5.37  
% 11.67/5.37  %Background operators:
% 11.67/5.37  
% 11.67/5.37  
% 11.67/5.37  %Foreground operators:
% 11.67/5.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.67/5.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.67/5.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.67/5.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.67/5.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.67/5.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.67/5.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.67/5.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.67/5.37  tff('#skF_5', type, '#skF_5': $i).
% 11.67/5.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.67/5.37  tff('#skF_3', type, '#skF_3': $i).
% 11.67/5.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.67/5.37  tff('#skF_4', type, '#skF_4': $i).
% 11.67/5.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.67/5.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.67/5.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.67/5.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.67/5.37  
% 11.79/5.38  tff(f_80, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 11.79/5.38  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 11.79/5.38  tff(f_71, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 11.79/5.38  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.79/5.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.79/5.38  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 11.79/5.38  tff(f_52, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 11.79/5.38  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 11.79/5.38  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.79/5.38  tff(c_44, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.79/5.38  tff(c_30, plain, (![B_26, A_25]: (k3_xboole_0(B_26, k1_tarski(A_25))=k1_tarski(A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.79/5.38  tff(c_36, plain, (![C_29, B_28]: (r1_tarski(k1_tarski(C_29), k2_tarski(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.79/5.38  tff(c_126, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.79/5.38  tff(c_142, plain, (![C_29, B_28]: (k3_xboole_0(k1_tarski(C_29), k2_tarski(B_28, C_29))=k1_tarski(C_29))), inference(resolution, [status(thm)], [c_36, c_126])).
% 11.79/5.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.79/5.38  tff(c_317, plain, (![A_67, B_68, C_69]: (k3_xboole_0(k3_xboole_0(A_67, B_68), C_69)=k3_xboole_0(A_67, k3_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.79/5.38  tff(c_1689, plain, (![B_121, A_122, B_123]: (k3_xboole_0(B_121, k3_xboole_0(A_122, B_123))=k3_xboole_0(A_122, k3_xboole_0(B_123, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_317])).
% 11.79/5.38  tff(c_46, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.79/5.38  tff(c_385, plain, (![C_69]: (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k3_xboole_0('#skF_5', C_69))=k3_xboole_0(k1_tarski('#skF_3'), C_69))), inference(superposition, [status(thm), theory('equality')], [c_46, c_317])).
% 11.79/5.38  tff(c_4415, plain, (![B_150]: (k3_xboole_0('#skF_5', k3_xboole_0(B_150, k2_tarski('#skF_3', '#skF_4')))=k3_xboole_0(k1_tarski('#skF_3'), B_150))), inference(superposition, [status(thm), theory('equality')], [c_1689, c_385])).
% 11.79/5.38  tff(c_4509, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k3_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_4415])).
% 11.79/5.38  tff(c_4581, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4509, c_30])).
% 11.79/5.38  tff(c_18422, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_4581])).
% 11.79/5.38  tff(c_2413, plain, (![A_125]: (k3_xboole_0('#skF_5', k3_xboole_0(A_125, k2_tarski('#skF_3', '#skF_4')))=k3_xboole_0(A_125, k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1689])).
% 11.79/5.38  tff(c_2483, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_2413])).
% 11.79/5.38  tff(c_247, plain, (![B_61, A_62]: (r2_hidden(B_61, A_62) | k3_xboole_0(A_62, k1_tarski(B_61))!=k1_tarski(B_61))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.79/5.38  tff(c_261, plain, (![B_61, B_2]: (r2_hidden(B_61, B_2) | k3_xboole_0(k1_tarski(B_61), B_2)!=k1_tarski(B_61))), inference(superposition, [status(thm), theory('equality')], [c_2, c_247])).
% 11.79/5.38  tff(c_3474, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3')) | k3_xboole_0('#skF_5', k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2483, c_261])).
% 11.79/5.38  tff(c_21168, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_18422, c_3474])).
% 11.79/5.38  tff(c_21171, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30, c_21168])).
% 11.79/5.38  tff(c_21175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_21171])).
% 11.79/5.38  tff(c_21177, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_4581])).
% 11.79/5.38  tff(c_8, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.79/5.38  tff(c_21190, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_21177, c_8])).
% 11.79/5.38  tff(c_21202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_21190])).
% 11.79/5.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.79/5.38  
% 11.79/5.38  Inference rules
% 11.79/5.38  ----------------------
% 11.79/5.38  #Ref     : 0
% 11.79/5.38  #Sup     : 5152
% 11.79/5.38  #Fact    : 0
% 11.79/5.38  #Define  : 0
% 11.79/5.38  #Split   : 3
% 11.79/5.38  #Chain   : 0
% 11.79/5.38  #Close   : 0
% 11.79/5.38  
% 11.79/5.38  Ordering : KBO
% 11.79/5.38  
% 11.79/5.38  Simplification rules
% 11.79/5.38  ----------------------
% 11.79/5.38  #Subsume      : 897
% 11.79/5.38  #Demod        : 5215
% 11.79/5.38  #Tautology    : 1954
% 11.79/5.38  #SimpNegUnit  : 77
% 11.79/5.38  #BackRed      : 3
% 11.79/5.38  
% 11.79/5.38  #Partial instantiations: 0
% 11.79/5.38  #Strategies tried      : 1
% 11.79/5.38  
% 11.79/5.38  Timing (in seconds)
% 11.79/5.38  ----------------------
% 11.79/5.38  Preprocessing        : 0.30
% 11.79/5.38  Parsing              : 0.15
% 11.79/5.38  CNF conversion       : 0.02
% 11.79/5.38  Main loop            : 4.32
% 11.79/5.38  Inferencing          : 0.69
% 11.79/5.38  Reduction            : 2.97
% 11.79/5.38  Demodulation         : 2.77
% 11.79/5.38  BG Simplification    : 0.11
% 11.79/5.38  Subsumption          : 0.43
% 11.79/5.38  Abstraction          : 0.16
% 11.79/5.38  MUC search           : 0.00
% 11.79/5.38  Cooper               : 0.00
% 11.79/5.38  Total                : 4.65
% 11.79/5.38  Index Insertion      : 0.00
% 11.79/5.38  Index Deletion       : 0.00
% 11.79/5.38  Index Matching       : 0.00
% 11.79/5.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
