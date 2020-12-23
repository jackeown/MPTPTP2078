%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:21 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  94 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_25,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_40,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_27] : r1_tarski(A_27,A_27) ),
    inference(resolution,[status(thm)],[c_40,c_4])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [C_36,B_37,A_38] :
      ( r2_hidden(C_36,B_37)
      | ~ r2_hidden(C_36,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_410,plain,(
    ! [A_67,B_68,B_69] :
      ( r2_hidden('#skF_1'(A_67,B_68),B_69)
      | ~ r1_tarski(A_67,B_69)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3282,plain,(
    ! [A_187,B_188,B_189,B_190] :
      ( r2_hidden('#skF_1'(A_187,B_188),B_189)
      | ~ r1_tarski(B_190,B_189)
      | ~ r1_tarski(A_187,B_190)
      | r1_tarski(A_187,B_188) ) ),
    inference(resolution,[status(thm)],[c_410,c_2])).

tff(c_3354,plain,(
    ! [A_193,B_194] :
      ( r2_hidden('#skF_1'(A_193,B_194),k4_xboole_0('#skF_3','#skF_4'))
      | ~ r1_tarski(A_193,'#skF_2')
      | r1_tarski(A_193,B_194) ) ),
    inference(resolution,[status(thm)],[c_22,c_3282])).

tff(c_3555,plain,(
    ! [A_201,B_202,B_203] :
      ( r2_hidden('#skF_1'(A_201,B_202),B_203)
      | ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),B_203)
      | ~ r1_tarski(A_201,'#skF_2')
      | r1_tarski(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_3354,c_2])).

tff(c_4020,plain,(
    ! [B_218,A_219] :
      ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),B_218)
      | ~ r1_tarski(A_219,'#skF_2')
      | r1_tarski(A_219,B_218) ) ),
    inference(resolution,[status(thm)],[c_3555,c_4])).

tff(c_4038,plain,(
    ! [A_220] :
      ( ~ r1_tarski(A_220,'#skF_2')
      | r1_tarski(A_220,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_4020])).

tff(c_4042,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_4038])).

tff(c_4050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_4042])).

tff(c_4051,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_4053,plain,(
    ! [A_221,B_222] :
      ( k3_xboole_0(A_221,B_222) = A_221
      | ~ r1_tarski(A_221,B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4065,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_4053])).

tff(c_4180,plain,(
    ! [A_237,B_238,C_239] : k4_xboole_0(k3_xboole_0(A_237,B_238),C_239) = k3_xboole_0(A_237,k4_xboole_0(B_238,C_239)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4211,plain,(
    ! [A_240,B_241,C_242] : r1_xboole_0(k3_xboole_0(A_240,k4_xboole_0(B_241,C_242)),C_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_4180,c_16])).

tff(c_4231,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4065,c_4211])).

tff(c_4234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4051,c_4231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:24:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/2.04  
% 4.75/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/2.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.75/2.04  
% 4.75/2.04  %Foreground sorts:
% 4.75/2.04  
% 4.75/2.04  
% 4.75/2.04  %Background operators:
% 4.75/2.04  
% 4.75/2.04  
% 4.75/2.04  %Foreground operators:
% 4.75/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.75/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.75/2.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.75/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.75/2.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.75/2.04  tff('#skF_2', type, '#skF_2': $i).
% 4.75/2.04  tff('#skF_3', type, '#skF_3': $i).
% 4.75/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/2.04  tff('#skF_4', type, '#skF_4': $i).
% 4.75/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.75/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.75/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.75/2.04  
% 4.75/2.05  tff(f_53, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.75/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.75/2.05  tff(f_40, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.75/2.05  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.75/2.05  tff(f_42, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.75/2.05  tff(f_44, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.75/2.05  tff(c_20, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.75/2.05  tff(c_25, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_20])).
% 4.75/2.05  tff(c_40, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.75/2.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.75/2.05  tff(c_45, plain, (![A_27]: (r1_tarski(A_27, A_27))), inference(resolution, [status(thm)], [c_40, c_4])).
% 4.75/2.05  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.75/2.05  tff(c_22, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.75/2.05  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.75/2.05  tff(c_112, plain, (![C_36, B_37, A_38]: (r2_hidden(C_36, B_37) | ~r2_hidden(C_36, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.75/2.05  tff(c_410, plain, (![A_67, B_68, B_69]: (r2_hidden('#skF_1'(A_67, B_68), B_69) | ~r1_tarski(A_67, B_69) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_6, c_112])).
% 4.75/2.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.75/2.05  tff(c_3282, plain, (![A_187, B_188, B_189, B_190]: (r2_hidden('#skF_1'(A_187, B_188), B_189) | ~r1_tarski(B_190, B_189) | ~r1_tarski(A_187, B_190) | r1_tarski(A_187, B_188))), inference(resolution, [status(thm)], [c_410, c_2])).
% 4.75/2.05  tff(c_3354, plain, (![A_193, B_194]: (r2_hidden('#skF_1'(A_193, B_194), k4_xboole_0('#skF_3', '#skF_4')) | ~r1_tarski(A_193, '#skF_2') | r1_tarski(A_193, B_194))), inference(resolution, [status(thm)], [c_22, c_3282])).
% 4.75/2.05  tff(c_3555, plain, (![A_201, B_202, B_203]: (r2_hidden('#skF_1'(A_201, B_202), B_203) | ~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), B_203) | ~r1_tarski(A_201, '#skF_2') | r1_tarski(A_201, B_202))), inference(resolution, [status(thm)], [c_3354, c_2])).
% 4.75/2.05  tff(c_4020, plain, (![B_218, A_219]: (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), B_218) | ~r1_tarski(A_219, '#skF_2') | r1_tarski(A_219, B_218))), inference(resolution, [status(thm)], [c_3555, c_4])).
% 4.75/2.05  tff(c_4038, plain, (![A_220]: (~r1_tarski(A_220, '#skF_2') | r1_tarski(A_220, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_4020])).
% 4.75/2.05  tff(c_4042, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_45, c_4038])).
% 4.75/2.05  tff(c_4050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_4042])).
% 4.75/2.05  tff(c_4051, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 4.75/2.05  tff(c_4053, plain, (![A_221, B_222]: (k3_xboole_0(A_221, B_222)=A_221 | ~r1_tarski(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.75/2.05  tff(c_4065, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_22, c_4053])).
% 4.75/2.05  tff(c_4180, plain, (![A_237, B_238, C_239]: (k4_xboole_0(k3_xboole_0(A_237, B_238), C_239)=k3_xboole_0(A_237, k4_xboole_0(B_238, C_239)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.75/2.05  tff(c_16, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.75/2.05  tff(c_4211, plain, (![A_240, B_241, C_242]: (r1_xboole_0(k3_xboole_0(A_240, k4_xboole_0(B_241, C_242)), C_242))), inference(superposition, [status(thm), theory('equality')], [c_4180, c_16])).
% 4.75/2.05  tff(c_4231, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4065, c_4211])).
% 4.75/2.05  tff(c_4234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4051, c_4231])).
% 4.75/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/2.05  
% 4.75/2.05  Inference rules
% 4.75/2.05  ----------------------
% 4.75/2.05  #Ref     : 0
% 4.75/2.05  #Sup     : 1052
% 4.75/2.05  #Fact    : 0
% 4.75/2.05  #Define  : 0
% 4.75/2.05  #Split   : 2
% 4.75/2.05  #Chain   : 0
% 4.75/2.05  #Close   : 0
% 4.75/2.05  
% 4.75/2.05  Ordering : KBO
% 4.75/2.05  
% 4.75/2.05  Simplification rules
% 4.75/2.05  ----------------------
% 4.75/2.05  #Subsume      : 29
% 4.75/2.05  #Demod        : 1179
% 4.75/2.05  #Tautology    : 672
% 4.75/2.05  #SimpNegUnit  : 2
% 4.75/2.05  #BackRed      : 11
% 4.75/2.05  
% 4.75/2.05  #Partial instantiations: 0
% 4.75/2.05  #Strategies tried      : 1
% 4.75/2.05  
% 4.75/2.05  Timing (in seconds)
% 4.75/2.05  ----------------------
% 4.75/2.05  Preprocessing        : 0.30
% 4.75/2.05  Parsing              : 0.17
% 4.75/2.05  CNF conversion       : 0.02
% 4.75/2.05  Main loop            : 0.94
% 4.75/2.05  Inferencing          : 0.30
% 4.75/2.05  Reduction            : 0.40
% 4.75/2.05  Demodulation         : 0.32
% 4.75/2.05  BG Simplification    : 0.03
% 4.75/2.05  Subsumption          : 0.15
% 4.75/2.05  Abstraction          : 0.05
% 4.75/2.05  MUC search           : 0.00
% 4.75/2.05  Cooper               : 0.00
% 4.75/2.05  Total                : 1.27
% 4.75/2.05  Index Insertion      : 0.00
% 4.75/2.05  Index Deletion       : 0.00
% 4.75/2.05  Index Matching       : 0.00
% 4.75/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
