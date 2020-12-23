%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:02 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   51 (  81 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  96 expanded)
%              Number of equality atoms :   17 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_109,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [E_11,B_6,C_7] : r2_hidden(E_11,k1_enumset1(E_11,B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_118,plain,(
    ! [A_40,B_41] : r2_hidden(A_40,k2_tarski(A_40,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16])).

tff(c_91,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,k3_tarski(B_18))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_658,plain,(
    ! [A_128,A_129,B_130] :
      ( r1_tarski(A_128,k2_xboole_0(A_129,B_130))
      | ~ r2_hidden(A_128,k2_tarski(A_129,B_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_38])).

tff(c_676,plain,(
    ! [A_40,B_41] : r1_tarski(A_40,k2_xboole_0(A_40,B_41)) ),
    inference(resolution,[status(thm)],[c_118,c_658])).

tff(c_8,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(B_50,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_40,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_170,plain,(
    ! [B_50,A_49] : k2_xboole_0(B_50,A_49) = k2_xboole_0(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_40])).

tff(c_50,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_51,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_3'),'#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_50])).

tff(c_190,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_3')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_51])).

tff(c_243,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_250,plain,
    ( k2_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_3')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_190,c_243])).

tff(c_341,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_341])).

tff(c_681,plain,(
    k2_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_3')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_12,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,(
    ! [B_41,A_40] : r2_hidden(B_41,k2_tarski(A_40,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_12])).

tff(c_146,plain,(
    ! [B_46,C_47,A_48] :
      ( r2_hidden(B_46,C_47)
      | ~ r1_tarski(k2_tarski(A_48,B_46),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_265,plain,(
    ! [B_61,B_62,A_63] :
      ( r2_hidden(B_61,k3_tarski(B_62))
      | ~ r2_hidden(k2_tarski(A_63,B_61),B_62) ) ),
    inference(resolution,[status(thm)],[c_38,c_146])).

tff(c_273,plain,(
    ! [B_61,A_40,A_63] : r2_hidden(B_61,k3_tarski(k2_tarski(A_40,k2_tarski(A_63,B_61)))) ),
    inference(resolution,[status(thm)],[c_115,c_265])).

tff(c_295,plain,(
    ! [B_61,A_40,A_63] : r2_hidden(B_61,k2_xboole_0(A_40,k2_tarski(A_63,B_61))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_273])).

tff(c_688,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_295])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.35  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.61/1.35  
% 2.61/1.35  %Foreground sorts:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Background operators:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Foreground operators:
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.61/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.61/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.61/1.35  
% 2.71/1.36  tff(f_69, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.71/1.36  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.71/1.36  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.71/1.36  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.71/1.36  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.71/1.36  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.71/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.71/1.36  tff(f_64, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.71/1.36  tff(c_48, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.36  tff(c_109, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.71/1.36  tff(c_16, plain, (![E_11, B_6, C_7]: (r2_hidden(E_11, k1_enumset1(E_11, B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.71/1.36  tff(c_118, plain, (![A_40, B_41]: (r2_hidden(A_40, k2_tarski(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_16])).
% 2.71/1.36  tff(c_91, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.36  tff(c_38, plain, (![A_17, B_18]: (r1_tarski(A_17, k3_tarski(B_18)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.71/1.36  tff(c_658, plain, (![A_128, A_129, B_130]: (r1_tarski(A_128, k2_xboole_0(A_129, B_130)) | ~r2_hidden(A_128, k2_tarski(A_129, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_38])).
% 2.71/1.36  tff(c_676, plain, (![A_40, B_41]: (r1_tarski(A_40, k2_xboole_0(A_40, B_41)))), inference(resolution, [status(thm)], [c_118, c_658])).
% 2.71/1.36  tff(c_8, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.36  tff(c_164, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(B_50, A_49))), inference(superposition, [status(thm), theory('equality')], [c_8, c_91])).
% 2.71/1.36  tff(c_40, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.36  tff(c_170, plain, (![B_50, A_49]: (k2_xboole_0(B_50, A_49)=k2_xboole_0(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_164, c_40])).
% 2.71/1.36  tff(c_50, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.36  tff(c_51, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_3'), '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_50])).
% 2.71/1.36  tff(c_190, plain, (r1_tarski(k2_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_3')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_51])).
% 2.71/1.36  tff(c_243, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.36  tff(c_250, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_3'))='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_190, c_243])).
% 2.71/1.36  tff(c_341, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_250])).
% 2.71/1.36  tff(c_680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_676, c_341])).
% 2.71/1.36  tff(c_681, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_3'))='#skF_5'), inference(splitRight, [status(thm)], [c_250])).
% 2.71/1.36  tff(c_12, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.71/1.36  tff(c_115, plain, (![B_41, A_40]: (r2_hidden(B_41, k2_tarski(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_12])).
% 2.71/1.36  tff(c_146, plain, (![B_46, C_47, A_48]: (r2_hidden(B_46, C_47) | ~r1_tarski(k2_tarski(A_48, B_46), C_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.36  tff(c_265, plain, (![B_61, B_62, A_63]: (r2_hidden(B_61, k3_tarski(B_62)) | ~r2_hidden(k2_tarski(A_63, B_61), B_62))), inference(resolution, [status(thm)], [c_38, c_146])).
% 2.71/1.36  tff(c_273, plain, (![B_61, A_40, A_63]: (r2_hidden(B_61, k3_tarski(k2_tarski(A_40, k2_tarski(A_63, B_61)))))), inference(resolution, [status(thm)], [c_115, c_265])).
% 2.71/1.36  tff(c_295, plain, (![B_61, A_40, A_63]: (r2_hidden(B_61, k2_xboole_0(A_40, k2_tarski(A_63, B_61))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_273])).
% 2.71/1.36  tff(c_688, plain, (r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_681, c_295])).
% 2.71/1.36  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_688])).
% 2.71/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.36  
% 2.71/1.36  Inference rules
% 2.71/1.36  ----------------------
% 2.71/1.36  #Ref     : 0
% 2.71/1.36  #Sup     : 140
% 2.71/1.36  #Fact    : 0
% 2.71/1.36  #Define  : 0
% 2.71/1.36  #Split   : 1
% 2.71/1.36  #Chain   : 0
% 2.71/1.36  #Close   : 0
% 2.71/1.36  
% 2.71/1.36  Ordering : KBO
% 2.71/1.36  
% 2.71/1.36  Simplification rules
% 2.71/1.36  ----------------------
% 2.71/1.36  #Subsume      : 11
% 2.71/1.36  #Demod        : 63
% 2.71/1.36  #Tautology    : 78
% 2.71/1.36  #SimpNegUnit  : 1
% 2.71/1.36  #BackRed      : 3
% 2.71/1.36  
% 2.71/1.36  #Partial instantiations: 0
% 2.71/1.36  #Strategies tried      : 1
% 2.71/1.36  
% 2.71/1.36  Timing (in seconds)
% 2.71/1.36  ----------------------
% 2.71/1.37  Preprocessing        : 0.30
% 2.71/1.37  Parsing              : 0.15
% 2.71/1.37  CNF conversion       : 0.02
% 2.71/1.37  Main loop            : 0.30
% 2.71/1.37  Inferencing          : 0.10
% 2.71/1.37  Reduction            : 0.11
% 2.71/1.37  Demodulation         : 0.09
% 2.71/1.37  BG Simplification    : 0.02
% 2.71/1.37  Subsumption          : 0.06
% 2.71/1.37  Abstraction          : 0.02
% 2.71/1.37  MUC search           : 0.00
% 2.71/1.37  Cooper               : 0.00
% 2.71/1.37  Total                : 0.63
% 2.71/1.37  Index Insertion      : 0.00
% 2.71/1.37  Index Deletion       : 0.00
% 2.71/1.37  Index Matching       : 0.00
% 2.71/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
