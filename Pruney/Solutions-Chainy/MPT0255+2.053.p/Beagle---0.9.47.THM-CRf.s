%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:46 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   54 (  92 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 ( 100 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_76,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,A_49) = k2_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_186,plain,(
    ! [A_53,B_54] : r1_tarski(A_53,k2_xboole_0(B_54,A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_16])).

tff(c_198,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_186])).

tff(c_249,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_268,plain,(
    k3_xboole_0('#skF_7',k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_198,c_249])).

tff(c_405,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,k3_xboole_0(A_71,B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_420,plain,(
    ! [C_73] :
      ( ~ r1_xboole_0('#skF_7',k1_xboole_0)
      | ~ r2_hidden(C_73,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_405])).

tff(c_431,plain,(
    ! [C_73] : ~ r2_hidden(C_73,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_420])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_433,plain,(
    ! [C_74] : ~ r2_hidden(C_74,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_420])).

tff(c_438,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_8,c_433])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_493,plain,(
    ! [A_77] : k2_xboole_0(A_77,'#skF_7') = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_10])).

tff(c_448,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_50])).

tff(c_499,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_448])).

tff(c_231,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [E_22,A_16,B_17] : r2_hidden(E_22,k1_enumset1(A_16,B_17,E_22)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_243,plain,(
    ! [B_58,A_57] : r2_hidden(B_58,k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_20])).

tff(c_645,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_243])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_431,c_645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.38  
% 2.45/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.45/1.38  
% 2.45/1.38  %Foreground sorts:
% 2.45/1.38  
% 2.45/1.38  
% 2.45/1.38  %Background operators:
% 2.45/1.38  
% 2.45/1.38  
% 2.45/1.38  %Foreground operators:
% 2.45/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.45/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.45/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.45/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.45/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.38  
% 2.45/1.39  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.45/1.39  tff(f_86, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.45/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.45/1.39  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.45/1.39  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.45/1.39  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.45/1.39  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.45/1.39  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.45/1.39  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.45/1.39  tff(f_74, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.45/1.39  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.45/1.39  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.45/1.39  tff(c_76, plain, (![B_48, A_49]: (k2_xboole_0(B_48, A_49)=k2_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.39  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.39  tff(c_186, plain, (![A_53, B_54]: (r1_tarski(A_53, k2_xboole_0(B_54, A_53)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_16])).
% 2.45/1.39  tff(c_198, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_186])).
% 2.45/1.39  tff(c_249, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.45/1.39  tff(c_268, plain, (k3_xboole_0('#skF_7', k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_198, c_249])).
% 2.45/1.39  tff(c_405, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, k3_xboole_0(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.39  tff(c_420, plain, (![C_73]: (~r1_xboole_0('#skF_7', k1_xboole_0) | ~r2_hidden(C_73, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_268, c_405])).
% 2.45/1.39  tff(c_431, plain, (![C_73]: (~r2_hidden(C_73, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_420])).
% 2.45/1.39  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.45/1.39  tff(c_433, plain, (![C_74]: (~r2_hidden(C_74, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_420])).
% 2.45/1.39  tff(c_438, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_8, c_433])).
% 2.45/1.39  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.39  tff(c_493, plain, (![A_77]: (k2_xboole_0(A_77, '#skF_7')=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_438, c_10])).
% 2.45/1.39  tff(c_448, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_438, c_50])).
% 2.45/1.39  tff(c_499, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_493, c_448])).
% 2.45/1.39  tff(c_231, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.45/1.39  tff(c_20, plain, (![E_22, A_16, B_17]: (r2_hidden(E_22, k1_enumset1(A_16, B_17, E_22)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.39  tff(c_243, plain, (![B_58, A_57]: (r2_hidden(B_58, k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_231, c_20])).
% 2.45/1.39  tff(c_645, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_499, c_243])).
% 2.45/1.39  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_431, c_645])).
% 2.45/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.39  
% 2.45/1.39  Inference rules
% 2.45/1.39  ----------------------
% 2.45/1.39  #Ref     : 0
% 2.45/1.39  #Sup     : 148
% 2.45/1.39  #Fact    : 0
% 2.45/1.39  #Define  : 0
% 2.45/1.39  #Split   : 0
% 2.45/1.39  #Chain   : 0
% 2.45/1.39  #Close   : 0
% 2.45/1.39  
% 2.45/1.39  Ordering : KBO
% 2.45/1.39  
% 2.45/1.39  Simplification rules
% 2.45/1.39  ----------------------
% 2.45/1.39  #Subsume      : 1
% 2.45/1.39  #Demod        : 61
% 2.45/1.39  #Tautology    : 108
% 2.45/1.39  #SimpNegUnit  : 1
% 2.45/1.39  #BackRed      : 13
% 2.45/1.39  
% 2.45/1.39  #Partial instantiations: 0
% 2.45/1.39  #Strategies tried      : 1
% 2.45/1.39  
% 2.45/1.39  Timing (in seconds)
% 2.45/1.39  ----------------------
% 2.45/1.40  Preprocessing        : 0.34
% 2.45/1.40  Parsing              : 0.17
% 2.45/1.40  CNF conversion       : 0.03
% 2.45/1.40  Main loop            : 0.25
% 2.45/1.40  Inferencing          : 0.08
% 2.45/1.40  Reduction            : 0.09
% 2.45/1.40  Demodulation         : 0.07
% 2.45/1.40  BG Simplification    : 0.02
% 2.45/1.40  Subsumption          : 0.04
% 2.45/1.40  Abstraction          : 0.02
% 2.45/1.40  MUC search           : 0.00
% 2.45/1.40  Cooper               : 0.00
% 2.45/1.40  Total                : 0.61
% 2.45/1.40  Index Insertion      : 0.00
% 2.45/1.40  Index Deletion       : 0.00
% 2.45/1.40  Index Matching       : 0.00
% 2.45/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
