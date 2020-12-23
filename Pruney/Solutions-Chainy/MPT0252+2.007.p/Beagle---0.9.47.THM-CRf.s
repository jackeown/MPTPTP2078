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
% DateTime   : Thu Dec  3 09:51:02 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   51 (  65 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  67 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_62,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_151,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_163,plain,(
    ! [B_51,A_50] : r2_hidden(B_51,k2_tarski(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_34])).

tff(c_28,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_136,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_202,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(B_60,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_136])).

tff(c_60,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_208,plain,(
    ! [B_60,A_59] : k2_xboole_0(B_60,A_59) = k2_xboole_0(A_59,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_60])).

tff(c_64,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_65,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_64])).

tff(c_226,plain,(
    r1_tarski(k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_65])).

tff(c_333,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_335,plain,
    ( k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_226,c_333])).

tff(c_344,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_335])).

tff(c_105,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_112,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(resolution,[status(thm)],[c_28,c_105])).

tff(c_177,plain,(
    ! [D_54,B_55,A_56] :
      ( r2_hidden(D_54,B_55)
      | ~ r2_hidden(D_54,k3_xboole_0(A_56,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_378,plain,(
    ! [D_72,A_73,B_74] :
      ( r2_hidden(D_72,k2_xboole_0(A_73,B_74))
      | ~ r2_hidden(D_72,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_177])).

tff(c_397,plain,(
    ! [D_78,B_79,A_80] :
      ( r2_hidden(D_78,k2_xboole_0(B_79,A_80))
      | ~ r2_hidden(D_78,A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_378])).

tff(c_418,plain,(
    ! [D_81] :
      ( r2_hidden(D_81,'#skF_7')
      | ~ r2_hidden(D_81,k2_tarski('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_397])).

tff(c_422,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_163,c_418])).

tff(c_430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:57:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.32  
% 2.36/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.32  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.36/1.32  
% 2.36/1.32  %Foreground sorts:
% 2.36/1.32  
% 2.36/1.32  
% 2.36/1.32  %Background operators:
% 2.36/1.32  
% 2.36/1.32  
% 2.36/1.32  %Foreground operators:
% 2.36/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.36/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.36/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.36/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.36/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.36/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.36/1.32  
% 2.36/1.34  tff(f_74, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.36/1.34  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.36/1.34  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.36/1.34  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.36/1.34  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.36/1.34  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.36/1.34  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.34  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.36/1.34  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.36/1.34  tff(c_62, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.34  tff(c_151, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.36/1.34  tff(c_34, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.34  tff(c_163, plain, (![B_51, A_50]: (r2_hidden(B_51, k2_tarski(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_34])).
% 2.36/1.34  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.34  tff(c_30, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.34  tff(c_136, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.36/1.34  tff(c_202, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(B_60, A_59))), inference(superposition, [status(thm), theory('equality')], [c_30, c_136])).
% 2.36/1.34  tff(c_60, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.36/1.34  tff(c_208, plain, (![B_60, A_59]: (k2_xboole_0(B_60, A_59)=k2_xboole_0(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_202, c_60])).
% 2.36/1.34  tff(c_64, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.34  tff(c_65, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_64])).
% 2.36/1.34  tff(c_226, plain, (r1_tarski(k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_65])).
% 2.36/1.34  tff(c_333, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.36/1.34  tff(c_335, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5'))='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_226, c_333])).
% 2.36/1.34  tff(c_344, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_335])).
% 2.36/1.34  tff(c_105, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.34  tff(c_112, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(resolution, [status(thm)], [c_28, c_105])).
% 2.36/1.34  tff(c_177, plain, (![D_54, B_55, A_56]: (r2_hidden(D_54, B_55) | ~r2_hidden(D_54, k3_xboole_0(A_56, B_55)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.34  tff(c_378, plain, (![D_72, A_73, B_74]: (r2_hidden(D_72, k2_xboole_0(A_73, B_74)) | ~r2_hidden(D_72, A_73))), inference(superposition, [status(thm), theory('equality')], [c_112, c_177])).
% 2.36/1.34  tff(c_397, plain, (![D_78, B_79, A_80]: (r2_hidden(D_78, k2_xboole_0(B_79, A_80)) | ~r2_hidden(D_78, A_80))), inference(superposition, [status(thm), theory('equality')], [c_208, c_378])).
% 2.36/1.34  tff(c_418, plain, (![D_81]: (r2_hidden(D_81, '#skF_7') | ~r2_hidden(D_81, k2_tarski('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_344, c_397])).
% 2.36/1.34  tff(c_422, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_163, c_418])).
% 2.36/1.34  tff(c_430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_422])).
% 2.36/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.34  
% 2.36/1.34  Inference rules
% 2.36/1.34  ----------------------
% 2.36/1.34  #Ref     : 0
% 2.36/1.34  #Sup     : 91
% 2.36/1.34  #Fact    : 0
% 2.36/1.34  #Define  : 0
% 2.36/1.34  #Split   : 0
% 2.36/1.34  #Chain   : 0
% 2.36/1.34  #Close   : 0
% 2.36/1.34  
% 2.36/1.34  Ordering : KBO
% 2.36/1.34  
% 2.36/1.34  Simplification rules
% 2.36/1.34  ----------------------
% 2.36/1.34  #Subsume      : 5
% 2.36/1.34  #Demod        : 28
% 2.36/1.34  #Tautology    : 65
% 2.36/1.34  #SimpNegUnit  : 1
% 2.36/1.34  #BackRed      : 3
% 2.36/1.34  
% 2.36/1.34  #Partial instantiations: 0
% 2.36/1.34  #Strategies tried      : 1
% 2.36/1.34  
% 2.36/1.34  Timing (in seconds)
% 2.36/1.34  ----------------------
% 2.36/1.34  Preprocessing        : 0.33
% 2.36/1.34  Parsing              : 0.17
% 2.36/1.34  CNF conversion       : 0.02
% 2.36/1.34  Main loop            : 0.23
% 2.36/1.34  Inferencing          : 0.07
% 2.36/1.34  Reduction            : 0.09
% 2.36/1.34  Demodulation         : 0.07
% 2.36/1.34  BG Simplification    : 0.02
% 2.36/1.34  Subsumption          : 0.04
% 2.36/1.34  Abstraction          : 0.01
% 2.36/1.34  MUC search           : 0.00
% 2.36/1.34  Cooper               : 0.00
% 2.36/1.34  Total                : 0.59
% 2.36/1.34  Index Insertion      : 0.00
% 2.36/1.34  Index Deletion       : 0.00
% 2.36/1.34  Index Matching       : 0.00
% 2.36/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
