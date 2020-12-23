%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:47 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 255 expanded)
%              Number of leaves         :   28 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :   65 ( 470 expanded)
%              Number of equality atoms :   12 ( 152 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
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

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_34,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ! [D_26,A_21] : r2_hidden(D_26,k2_tarski(A_21,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_143,plain,(
    ! [D_50,A_51,B_52] :
      ( ~ r2_hidden(D_50,A_51)
      | r2_hidden(D_50,k2_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_186,plain,(
    ! [D_59] :
      ( ~ r2_hidden(D_59,k2_tarski('#skF_7','#skF_8'))
      | r2_hidden(D_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_143])).

tff(c_205,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_186])).

tff(c_235,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_243,plain,(
    ! [B_69] :
      ( r2_hidden('#skF_8',B_69)
      | ~ r1_tarski(k1_xboole_0,B_69) ) ),
    inference(resolution,[status(thm)],[c_205,c_235])).

tff(c_267,plain,(
    ! [B_69] : r2_hidden('#skF_8',B_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_243])).

tff(c_324,plain,(
    ! [D_75,B_76,A_77] :
      ( D_75 = B_76
      | D_75 = A_77
      | ~ r2_hidden(D_75,k2_tarski(A_77,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_351,plain,(
    ! [B_76,A_77] :
      ( B_76 = '#skF_8'
      | A_77 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_267,c_324])).

tff(c_361,plain,(
    ! [A_78] : A_78 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_436,plain,(
    ! [A_19] : r1_tarski('#skF_8',A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_34])).

tff(c_42,plain,(
    ! [D_26,B_22] : r2_hidden(D_26,k2_tarski(D_26,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_471,plain,(
    ! [D_1048] : r2_hidden(D_1048,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_42])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_473,plain,(
    ! [D_1048,B_4] :
      ( r2_hidden(D_1048,B_4)
      | ~ r1_tarski('#skF_8',B_4) ) ),
    inference(resolution,[status(thm)],[c_471,c_4])).

tff(c_480,plain,(
    ! [D_1048,B_4] : r2_hidden(D_1048,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_473])).

tff(c_28,plain,(
    ! [A_14,B_15,C_18] :
      ( ~ r1_xboole_0(A_14,B_15)
      | ~ r2_hidden(C_18,B_15)
      | ~ r2_hidden(C_18,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_505,plain,(
    ! [A_14,B_15] : ~ r1_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_480,c_28])).

tff(c_36,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_438,plain,(
    ! [A_20] : r1_xboole_0(A_20,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_36])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_438])).

tff(c_552,plain,(
    ! [B_1196] : B_1196 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_627,plain,(
    ! [A_19] : r1_tarski('#skF_8',A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_34])).

tff(c_674,plain,(
    ! [D_2183] : r2_hidden(D_2183,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_42])).

tff(c_676,plain,(
    ! [D_2183,B_4] :
      ( r2_hidden(D_2183,B_4)
      | ~ r1_tarski('#skF_8',B_4) ) ),
    inference(resolution,[status(thm)],[c_674,c_4])).

tff(c_683,plain,(
    ! [D_2183,B_4] : r2_hidden(D_2183,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_676])).

tff(c_699,plain,(
    ! [A_14,B_15] : ~ r1_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_683,c_28])).

tff(c_629,plain,(
    ! [A_20] : r1_xboole_0(A_20,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_36])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_699,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_4
% 2.65/1.37  
% 2.65/1.37  %Foreground sorts:
% 2.65/1.37  
% 2.65/1.37  
% 2.65/1.37  %Background operators:
% 2.65/1.37  
% 2.65/1.37  
% 2.65/1.37  %Foreground operators:
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.37  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.65/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.65/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.65/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.65/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.65/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.65/1.37  
% 2.93/1.38  tff(f_63, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.93/1.38  tff(f_74, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.93/1.38  tff(f_84, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.93/1.38  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.93/1.38  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.93/1.38  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.93/1.38  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.93/1.38  tff(c_34, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.93/1.38  tff(c_40, plain, (![D_26, A_21]: (r2_hidden(D_26, k2_tarski(A_21, D_26)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.93/1.38  tff(c_62, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.93/1.38  tff(c_143, plain, (![D_50, A_51, B_52]: (~r2_hidden(D_50, A_51) | r2_hidden(D_50, k2_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.93/1.38  tff(c_186, plain, (![D_59]: (~r2_hidden(D_59, k2_tarski('#skF_7', '#skF_8')) | r2_hidden(D_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_143])).
% 2.93/1.38  tff(c_205, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_186])).
% 2.93/1.38  tff(c_235, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.93/1.38  tff(c_243, plain, (![B_69]: (r2_hidden('#skF_8', B_69) | ~r1_tarski(k1_xboole_0, B_69))), inference(resolution, [status(thm)], [c_205, c_235])).
% 2.93/1.38  tff(c_267, plain, (![B_69]: (r2_hidden('#skF_8', B_69))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_243])).
% 2.93/1.38  tff(c_324, plain, (![D_75, B_76, A_77]: (D_75=B_76 | D_75=A_77 | ~r2_hidden(D_75, k2_tarski(A_77, B_76)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.93/1.38  tff(c_351, plain, (![B_76, A_77]: (B_76='#skF_8' | A_77='#skF_8')), inference(resolution, [status(thm)], [c_267, c_324])).
% 2.93/1.38  tff(c_361, plain, (![A_78]: (A_78='#skF_8')), inference(splitLeft, [status(thm)], [c_351])).
% 2.93/1.38  tff(c_436, plain, (![A_19]: (r1_tarski('#skF_8', A_19))), inference(superposition, [status(thm), theory('equality')], [c_361, c_34])).
% 2.93/1.38  tff(c_42, plain, (![D_26, B_22]: (r2_hidden(D_26, k2_tarski(D_26, B_22)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.93/1.38  tff(c_471, plain, (![D_1048]: (r2_hidden(D_1048, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_361, c_42])).
% 2.93/1.38  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.93/1.38  tff(c_473, plain, (![D_1048, B_4]: (r2_hidden(D_1048, B_4) | ~r1_tarski('#skF_8', B_4))), inference(resolution, [status(thm)], [c_471, c_4])).
% 2.93/1.38  tff(c_480, plain, (![D_1048, B_4]: (r2_hidden(D_1048, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_473])).
% 2.93/1.38  tff(c_28, plain, (![A_14, B_15, C_18]: (~r1_xboole_0(A_14, B_15) | ~r2_hidden(C_18, B_15) | ~r2_hidden(C_18, A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.38  tff(c_505, plain, (![A_14, B_15]: (~r1_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_480, c_28])).
% 2.93/1.38  tff(c_36, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.93/1.38  tff(c_438, plain, (![A_20]: (r1_xboole_0(A_20, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_361, c_36])).
% 2.93/1.38  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_505, c_438])).
% 2.93/1.38  tff(c_552, plain, (![B_1196]: (B_1196='#skF_8')), inference(splitRight, [status(thm)], [c_351])).
% 2.93/1.38  tff(c_627, plain, (![A_19]: (r1_tarski('#skF_8', A_19))), inference(superposition, [status(thm), theory('equality')], [c_552, c_34])).
% 2.93/1.38  tff(c_674, plain, (![D_2183]: (r2_hidden(D_2183, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_552, c_42])).
% 2.93/1.38  tff(c_676, plain, (![D_2183, B_4]: (r2_hidden(D_2183, B_4) | ~r1_tarski('#skF_8', B_4))), inference(resolution, [status(thm)], [c_674, c_4])).
% 2.93/1.38  tff(c_683, plain, (![D_2183, B_4]: (r2_hidden(D_2183, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_627, c_676])).
% 2.93/1.38  tff(c_699, plain, (![A_14, B_15]: (~r1_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_683, c_28])).
% 2.93/1.38  tff(c_629, plain, (![A_20]: (r1_xboole_0(A_20, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_552, c_36])).
% 2.93/1.38  tff(c_723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_699, c_629])).
% 2.93/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.38  
% 2.93/1.38  Inference rules
% 2.93/1.38  ----------------------
% 2.93/1.38  #Ref     : 0
% 2.93/1.38  #Sup     : 179
% 2.93/1.38  #Fact    : 0
% 2.93/1.38  #Define  : 0
% 2.93/1.38  #Split   : 1
% 2.93/1.38  #Chain   : 0
% 2.93/1.38  #Close   : 0
% 2.93/1.38  
% 2.93/1.38  Ordering : KBO
% 2.93/1.38  
% 2.93/1.38  Simplification rules
% 2.93/1.38  ----------------------
% 2.93/1.38  #Subsume      : 26
% 2.93/1.38  #Demod        : 104
% 2.93/1.38  #Tautology    : 101
% 2.93/1.38  #SimpNegUnit  : 4
% 2.93/1.38  #BackRed      : 10
% 2.93/1.38  
% 2.93/1.38  #Partial instantiations: 0
% 2.93/1.38  #Strategies tried      : 1
% 2.93/1.38  
% 2.93/1.38  Timing (in seconds)
% 2.93/1.38  ----------------------
% 2.93/1.39  Preprocessing        : 0.31
% 2.93/1.39  Parsing              : 0.16
% 2.93/1.39  CNF conversion       : 0.02
% 2.93/1.39  Main loop            : 0.33
% 2.93/1.39  Inferencing          : 0.12
% 2.93/1.39  Reduction            : 0.10
% 2.93/1.39  Demodulation         : 0.08
% 2.93/1.39  BG Simplification    : 0.02
% 2.93/1.39  Subsumption          : 0.06
% 2.93/1.39  Abstraction          : 0.02
% 2.93/1.39  MUC search           : 0.00
% 2.93/1.39  Cooper               : 0.00
% 2.93/1.39  Total                : 0.66
% 2.93/1.39  Index Insertion      : 0.00
% 2.93/1.39  Index Deletion       : 0.00
% 2.93/1.39  Index Matching       : 0.00
% 2.93/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
