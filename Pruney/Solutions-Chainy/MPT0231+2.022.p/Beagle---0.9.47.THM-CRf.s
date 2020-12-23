%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:17 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 ( 113 expanded)
%              Number of equality atoms :   29 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_48,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,(
    ! [B_58,A_59] :
      ( k1_tarski(B_58) = A_59
      | k1_xboole_0 = A_59
      | ~ r1_tarski(A_59,k1_tarski(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_130,plain,
    ( k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_6')
    | k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_120])).

tff(c_190,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_66,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_78,plain,(
    ! [B_40,A_39] : r2_hidden(B_40,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_12])).

tff(c_197,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_78])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,B_54)
      | ~ r2_hidden(C_55,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [C_55,A_6] :
      ( ~ r2_hidden(C_55,k1_xboole_0)
      | ~ r2_hidden(C_55,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_206,plain,(
    ! [A_6] : ~ r2_hidden('#skF_5',A_6) ),
    inference(resolution,[status(thm)],[c_197,c_109])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_197])).

tff(c_212,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_16,plain,(
    ! [E_13,B_8,C_9] : r2_hidden(E_13,k1_enumset1(E_13,B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_72,plain,(
    ! [A_39,B_40] : r2_hidden(A_39,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_16])).

tff(c_253,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_72])).

tff(c_34,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_214,plain,(
    ! [E_67,C_68,B_69,A_70] :
      ( E_67 = C_68
      | E_67 = B_69
      | E_67 = A_70
      | ~ r2_hidden(E_67,k1_enumset1(A_70,B_69,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_257,plain,(
    ! [E_71,B_72,A_73] :
      ( E_71 = B_72
      | E_71 = A_73
      | E_71 = A_73
      | ~ r2_hidden(E_71,k2_tarski(A_73,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_214])).

tff(c_336,plain,(
    ! [E_79,A_80] :
      ( E_79 = A_80
      | E_79 = A_80
      | E_79 = A_80
      | ~ r2_hidden(E_79,k1_tarski(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_257])).

tff(c_339,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_253,c_336])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_48,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.42  
% 2.43/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.43/1.42  
% 2.43/1.42  %Foreground sorts:
% 2.43/1.42  
% 2.43/1.42  
% 2.43/1.42  %Background operators:
% 2.43/1.42  
% 2.43/1.42  
% 2.43/1.42  %Foreground operators:
% 2.43/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.43/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.43/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.43/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.43/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.43/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.42  
% 2.43/1.44  tff(f_79, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.43/1.44  tff(f_74, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.43/1.44  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.43/1.44  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.43/1.44  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.43/1.44  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.43/1.44  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.43/1.44  tff(c_48, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.43/1.44  tff(c_50, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.43/1.44  tff(c_120, plain, (![B_58, A_59]: (k1_tarski(B_58)=A_59 | k1_xboole_0=A_59 | ~r1_tarski(A_59, k1_tarski(B_58)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.43/1.44  tff(c_130, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_6') | k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_120])).
% 2.43/1.44  tff(c_190, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_130])).
% 2.43/1.44  tff(c_66, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.43/1.44  tff(c_12, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.43/1.44  tff(c_78, plain, (![B_40, A_39]: (r2_hidden(B_40, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_12])).
% 2.43/1.44  tff(c_197, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_190, c_78])).
% 2.43/1.44  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.44  tff(c_106, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, B_54) | ~r2_hidden(C_55, A_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.43/1.44  tff(c_109, plain, (![C_55, A_6]: (~r2_hidden(C_55, k1_xboole_0) | ~r2_hidden(C_55, A_6))), inference(resolution, [status(thm)], [c_8, c_106])).
% 2.43/1.44  tff(c_206, plain, (![A_6]: (~r2_hidden('#skF_5', A_6))), inference(resolution, [status(thm)], [c_197, c_109])).
% 2.43/1.44  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_197])).
% 2.43/1.44  tff(c_212, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_130])).
% 2.43/1.44  tff(c_16, plain, (![E_13, B_8, C_9]: (r2_hidden(E_13, k1_enumset1(E_13, B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.43/1.44  tff(c_72, plain, (![A_39, B_40]: (r2_hidden(A_39, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_16])).
% 2.43/1.44  tff(c_253, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_72])).
% 2.43/1.44  tff(c_34, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.43/1.44  tff(c_36, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.43/1.44  tff(c_214, plain, (![E_67, C_68, B_69, A_70]: (E_67=C_68 | E_67=B_69 | E_67=A_70 | ~r2_hidden(E_67, k1_enumset1(A_70, B_69, C_68)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.43/1.44  tff(c_257, plain, (![E_71, B_72, A_73]: (E_71=B_72 | E_71=A_73 | E_71=A_73 | ~r2_hidden(E_71, k2_tarski(A_73, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_214])).
% 2.43/1.44  tff(c_336, plain, (![E_79, A_80]: (E_79=A_80 | E_79=A_80 | E_79=A_80 | ~r2_hidden(E_79, k1_tarski(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_257])).
% 2.43/1.44  tff(c_339, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_253, c_336])).
% 2.43/1.44  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_48, c_339])).
% 2.43/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.44  
% 2.43/1.44  Inference rules
% 2.43/1.44  ----------------------
% 2.43/1.44  #Ref     : 0
% 2.43/1.44  #Sup     : 66
% 2.43/1.44  #Fact    : 0
% 2.43/1.44  #Define  : 0
% 2.43/1.44  #Split   : 1
% 2.43/1.44  #Chain   : 0
% 2.43/1.44  #Close   : 0
% 2.43/1.44  
% 2.43/1.44  Ordering : KBO
% 2.43/1.44  
% 2.43/1.44  Simplification rules
% 2.43/1.44  ----------------------
% 2.43/1.44  #Subsume      : 1
% 2.43/1.44  #Demod        : 23
% 2.43/1.44  #Tautology    : 42
% 2.43/1.44  #SimpNegUnit  : 3
% 2.43/1.44  #BackRed      : 7
% 2.43/1.44  
% 2.43/1.44  #Partial instantiations: 0
% 2.43/1.44  #Strategies tried      : 1
% 2.43/1.44  
% 2.43/1.44  Timing (in seconds)
% 2.43/1.44  ----------------------
% 2.43/1.45  Preprocessing        : 0.35
% 2.43/1.45  Parsing              : 0.18
% 2.43/1.45  CNF conversion       : 0.03
% 2.43/1.45  Main loop            : 0.30
% 2.43/1.45  Inferencing          : 0.11
% 2.43/1.45  Reduction            : 0.09
% 2.43/1.45  Demodulation         : 0.07
% 2.43/1.45  BG Simplification    : 0.02
% 2.43/1.45  Subsumption          : 0.06
% 2.43/1.45  Abstraction          : 0.01
% 2.43/1.45  MUC search           : 0.00
% 2.43/1.45  Cooper               : 0.00
% 2.43/1.45  Total                : 0.69
% 2.43/1.45  Index Insertion      : 0.00
% 2.43/1.45  Index Deletion       : 0.00
% 2.43/1.45  Index Matching       : 0.00
% 2.43/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
