%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:48 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :   47 (  80 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 154 expanded)
%              Number of equality atoms :   20 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_173,plain,(
    ! [A_43,B_44] : k2_xboole_0(k1_tarski(A_43),k1_tarski(B_44)) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_190,plain,(
    ! [A_43,B_44] : k2_tarski(A_43,B_44) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_40])).

tff(c_1743,plain,(
    ! [A_176,B_177,C_178] :
      ( r2_hidden('#skF_2'(A_176,B_177,C_178),B_177)
      | r2_hidden('#skF_2'(A_176,B_177,C_178),A_176)
      | r2_hidden('#skF_3'(A_176,B_177,C_178),C_178)
      | k2_xboole_0(A_176,B_177) = C_178 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4447,plain,(
    ! [A_281,B_282] :
      ( r2_hidden('#skF_2'(A_281,B_282,A_281),B_282)
      | r2_hidden('#skF_3'(A_281,B_282,A_281),A_281)
      | k2_xboole_0(A_281,B_282) = A_281 ) ),
    inference(resolution,[status(thm)],[c_1743,c_24])).

tff(c_1545,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden('#skF_2'(A_167,B_168,C_169),B_168)
      | r2_hidden('#skF_2'(A_167,B_168,C_169),A_167)
      | ~ r2_hidden('#skF_3'(A_167,B_168,C_169),A_167)
      | k2_xboole_0(A_167,B_168) = C_169 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1654,plain,(
    ! [A_167,B_168] :
      ( r2_hidden('#skF_2'(A_167,B_168,A_167),B_168)
      | ~ r2_hidden('#skF_3'(A_167,B_168,A_167),A_167)
      | k2_xboole_0(A_167,B_168) = A_167 ) ),
    inference(resolution,[status(thm)],[c_1545,c_20])).

tff(c_5121,plain,(
    ! [A_297,B_298] :
      ( r2_hidden('#skF_2'(A_297,B_298,A_297),B_298)
      | k2_xboole_0(A_297,B_298) = A_297 ) ),
    inference(resolution,[status(thm)],[c_4447,c_1654])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_211,plain,(
    ! [D_47,B_48,A_49] :
      ( ~ r2_hidden(D_47,B_48)
      | r2_hidden(D_47,k2_xboole_0(A_49,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_233,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,'#skF_6')
      | r2_hidden(D_47,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_211])).

tff(c_412,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_418,plain,(
    ! [D_47,B_67] :
      ( r2_hidden(D_47,B_67)
      | ~ r1_tarski(k1_xboole_0,B_67)
      | ~ r2_hidden(D_47,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_233,c_412])).

tff(c_425,plain,(
    ! [D_47,B_67] :
      ( r2_hidden(D_47,B_67)
      | ~ r2_hidden(D_47,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_418])).

tff(c_5304,plain,(
    ! [A_301,B_302] :
      ( r2_hidden('#skF_2'(A_301,'#skF_6',A_301),B_302)
      | k2_xboole_0(A_301,'#skF_6') = A_301 ) ),
    inference(resolution,[status(thm)],[c_5121,c_425])).

tff(c_5364,plain,(
    ! [B_302] :
      ( r2_hidden('#skF_3'(B_302,'#skF_6',B_302),B_302)
      | k2_xboole_0(B_302,'#skF_6') = B_302 ) ),
    inference(resolution,[status(thm)],[c_5304,c_24])).

tff(c_5526,plain,(
    ! [B_307] :
      ( ~ r2_hidden('#skF_3'(B_307,'#skF_6',B_307),B_307)
      | k2_xboole_0(B_307,'#skF_6') = B_307 ) ),
    inference(resolution,[status(thm)],[c_5304,c_20])).

tff(c_5693,plain,(
    ! [B_310] : k2_xboole_0(B_310,'#skF_6') = B_310 ),
    inference(resolution,[status(thm)],[c_5364,c_5526])).

tff(c_5775,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5693,c_42])).

tff(c_5806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_5775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.72/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/2.41  
% 6.78/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.78/2.41  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.78/2.41  
% 6.78/2.41  %Foreground sorts:
% 6.78/2.41  
% 6.78/2.41  
% 6.78/2.41  %Background operators:
% 6.78/2.41  
% 6.78/2.41  
% 6.78/2.41  %Foreground operators:
% 6.78/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.78/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.78/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.78/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.78/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.78/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.78/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.78/2.41  tff('#skF_5', type, '#skF_5': $i).
% 6.78/2.41  tff('#skF_6', type, '#skF_6': $i).
% 6.78/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.78/2.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.78/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.78/2.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.78/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.78/2.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.78/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.78/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.78/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.78/2.41  
% 6.81/2.42  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 6.81/2.42  tff(f_58, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.81/2.42  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.81/2.42  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.81/2.42  tff(f_62, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 6.81/2.42  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.81/2.42  tff(c_173, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), k1_tarski(B_44))=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.81/2.42  tff(c_40, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.81/2.42  tff(c_190, plain, (![A_43, B_44]: (k2_tarski(A_43, B_44)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_173, c_40])).
% 6.81/2.42  tff(c_1743, plain, (![A_176, B_177, C_178]: (r2_hidden('#skF_2'(A_176, B_177, C_178), B_177) | r2_hidden('#skF_2'(A_176, B_177, C_178), A_176) | r2_hidden('#skF_3'(A_176, B_177, C_178), C_178) | k2_xboole_0(A_176, B_177)=C_178)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.81/2.42  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.81/2.42  tff(c_4447, plain, (![A_281, B_282]: (r2_hidden('#skF_2'(A_281, B_282, A_281), B_282) | r2_hidden('#skF_3'(A_281, B_282, A_281), A_281) | k2_xboole_0(A_281, B_282)=A_281)), inference(resolution, [status(thm)], [c_1743, c_24])).
% 6.81/2.42  tff(c_1545, plain, (![A_167, B_168, C_169]: (r2_hidden('#skF_2'(A_167, B_168, C_169), B_168) | r2_hidden('#skF_2'(A_167, B_168, C_169), A_167) | ~r2_hidden('#skF_3'(A_167, B_168, C_169), A_167) | k2_xboole_0(A_167, B_168)=C_169)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.81/2.42  tff(c_20, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.81/2.42  tff(c_1654, plain, (![A_167, B_168]: (r2_hidden('#skF_2'(A_167, B_168, A_167), B_168) | ~r2_hidden('#skF_3'(A_167, B_168, A_167), A_167) | k2_xboole_0(A_167, B_168)=A_167)), inference(resolution, [status(thm)], [c_1545, c_20])).
% 6.81/2.42  tff(c_5121, plain, (![A_297, B_298]: (r2_hidden('#skF_2'(A_297, B_298, A_297), B_298) | k2_xboole_0(A_297, B_298)=A_297)), inference(resolution, [status(thm)], [c_4447, c_1654])).
% 6.81/2.42  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.81/2.42  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.81/2.42  tff(c_211, plain, (![D_47, B_48, A_49]: (~r2_hidden(D_47, B_48) | r2_hidden(D_47, k2_xboole_0(A_49, B_48)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.81/2.42  tff(c_233, plain, (![D_47]: (~r2_hidden(D_47, '#skF_6') | r2_hidden(D_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_211])).
% 6.81/2.42  tff(c_412, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.81/2.42  tff(c_418, plain, (![D_47, B_67]: (r2_hidden(D_47, B_67) | ~r1_tarski(k1_xboole_0, B_67) | ~r2_hidden(D_47, '#skF_6'))), inference(resolution, [status(thm)], [c_233, c_412])).
% 6.81/2.42  tff(c_425, plain, (![D_47, B_67]: (r2_hidden(D_47, B_67) | ~r2_hidden(D_47, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_418])).
% 6.81/2.42  tff(c_5304, plain, (![A_301, B_302]: (r2_hidden('#skF_2'(A_301, '#skF_6', A_301), B_302) | k2_xboole_0(A_301, '#skF_6')=A_301)), inference(resolution, [status(thm)], [c_5121, c_425])).
% 6.81/2.42  tff(c_5364, plain, (![B_302]: (r2_hidden('#skF_3'(B_302, '#skF_6', B_302), B_302) | k2_xboole_0(B_302, '#skF_6')=B_302)), inference(resolution, [status(thm)], [c_5304, c_24])).
% 6.81/2.42  tff(c_5526, plain, (![B_307]: (~r2_hidden('#skF_3'(B_307, '#skF_6', B_307), B_307) | k2_xboole_0(B_307, '#skF_6')=B_307)), inference(resolution, [status(thm)], [c_5304, c_20])).
% 6.81/2.42  tff(c_5693, plain, (![B_310]: (k2_xboole_0(B_310, '#skF_6')=B_310)), inference(resolution, [status(thm)], [c_5364, c_5526])).
% 6.81/2.42  tff(c_5775, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5693, c_42])).
% 6.81/2.42  tff(c_5806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_5775])).
% 6.81/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.81/2.42  
% 6.81/2.42  Inference rules
% 6.81/2.42  ----------------------
% 6.81/2.42  #Ref     : 0
% 6.81/2.42  #Sup     : 1355
% 6.81/2.42  #Fact    : 6
% 6.81/2.42  #Define  : 0
% 6.81/2.42  #Split   : 0
% 6.81/2.42  #Chain   : 0
% 6.81/2.42  #Close   : 0
% 6.81/2.42  
% 6.81/2.42  Ordering : KBO
% 6.81/2.42  
% 6.81/2.42  Simplification rules
% 6.81/2.42  ----------------------
% 6.81/2.42  #Subsume      : 364
% 6.81/2.42  #Demod        : 302
% 6.81/2.42  #Tautology    : 236
% 6.81/2.42  #SimpNegUnit  : 8
% 6.81/2.42  #BackRed      : 12
% 6.81/2.42  
% 6.81/2.42  #Partial instantiations: 0
% 6.81/2.42  #Strategies tried      : 1
% 6.81/2.42  
% 6.81/2.42  Timing (in seconds)
% 6.81/2.42  ----------------------
% 6.81/2.42  Preprocessing        : 0.30
% 6.81/2.42  Parsing              : 0.15
% 6.81/2.42  CNF conversion       : 0.02
% 6.81/2.42  Main loop            : 1.36
% 6.81/2.42  Inferencing          : 0.39
% 6.81/2.42  Reduction            : 0.48
% 6.81/2.42  Demodulation         : 0.37
% 6.81/2.42  BG Simplification    : 0.05
% 6.81/2.42  Subsumption          : 0.36
% 6.81/2.42  Abstraction          : 0.06
% 6.81/2.42  MUC search           : 0.00
% 6.81/2.42  Cooper               : 0.00
% 6.81/2.42  Total                : 1.69
% 6.81/2.42  Index Insertion      : 0.00
% 6.81/2.42  Index Deletion       : 0.00
% 6.81/2.42  Index Matching       : 0.00
% 6.81/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
