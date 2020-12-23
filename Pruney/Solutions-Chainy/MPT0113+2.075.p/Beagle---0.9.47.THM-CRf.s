%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:21 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   61 (  96 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :   92 ( 162 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden('#skF_1'(A_32,B_33),B_33)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_20,plain,(
    ! [A_22,B_23] : r1_xboole_0(k4_xboole_0(A_22,B_23),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_163,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k4_xboole_0(A_65,B_66),C_67) = k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_193,plain,(
    ! [A_65,B_66,C_67] : r1_xboole_0(k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)),C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_20])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(A_46,k2_xboole_0(B_47,C_48))
      | ~ r1_tarski(k4_xboole_0(A_46,B_47),C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [A_46,B_47] : r1_tarski(A_46,k2_xboole_0(B_47,k4_xboole_0(A_46,B_47))) ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_95,plain,(
    ! [A_49,B_50] : r1_tarski(A_49,k2_xboole_0(B_50,A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_102,plain,(
    ! [B_9,A_8] : r1_tarski(k4_xboole_0(B_9,A_8),k2_xboole_0(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_95])).

tff(c_321,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(A_92,B_93)
      | ~ r1_xboole_0(A_92,C_94)
      | ~ r1_tarski(A_92,k2_xboole_0(B_93,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_877,plain,(
    ! [B_151,A_152] :
      ( r1_tarski(k4_xboole_0(B_151,A_152),A_152)
      | ~ r1_xboole_0(k4_xboole_0(B_151,A_152),B_151) ) ),
    inference(resolution,[status(thm)],[c_102,c_321])).

tff(c_1387,plain,(
    ! [C_174,B_175] : r1_tarski(k4_xboole_0(C_174,k2_xboole_0(B_175,C_174)),k2_xboole_0(B_175,C_174)) ),
    inference(resolution,[status(thm)],[c_193,c_877])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] :
      ( r1_tarski(A_19,B_20)
      | ~ r1_xboole_0(A_19,C_21)
      | ~ r1_tarski(A_19,k2_xboole_0(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1395,plain,(
    ! [C_174,B_175] :
      ( r1_tarski(k4_xboole_0(C_174,k2_xboole_0(B_175,C_174)),B_175)
      | ~ r1_xboole_0(k4_xboole_0(C_174,k2_xboole_0(B_175,C_174)),C_174) ) ),
    inference(resolution,[status(thm)],[c_1387,c_18])).

tff(c_1432,plain,(
    ! [C_176,B_177] : r1_tarski(k4_xboole_0(C_176,k2_xboole_0(B_177,C_176)),B_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_1395])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,k2_xboole_0(B_14,C_15))
      | ~ r1_tarski(k4_xboole_0(A_13,B_14),C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_181,plain,(
    ! [A_65,B_66,C_67,C_15] :
      ( r1_tarski(k4_xboole_0(A_65,B_66),k2_xboole_0(C_67,C_15))
      | ~ r1_tarski(k4_xboole_0(A_65,k2_xboole_0(B_66,C_67)),C_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_14])).

tff(c_1483,plain,(
    ! [C_178,B_179] : r1_tarski(k4_xboole_0(C_178,B_179),k2_xboole_0(C_178,B_179)) ),
    inference(resolution,[status(thm)],[c_1432,c_181])).

tff(c_1492,plain,(
    ! [C_178,B_179] :
      ( r1_tarski(k4_xboole_0(C_178,B_179),C_178)
      | ~ r1_xboole_0(k4_xboole_0(C_178,B_179),B_179) ) ),
    inference(resolution,[status(thm)],[c_1483,c_18])).

tff(c_1514,plain,(
    ! [C_178,B_179] : r1_tarski(k4_xboole_0(C_178,B_179),C_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1492])).

tff(c_24,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_53,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_389,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(A_100,B_102)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2664,plain,(
    ! [A_266,B_267,B_268,B_269] :
      ( r2_hidden('#skF_1'(A_266,B_267),B_268)
      | ~ r1_tarski(B_269,B_268)
      | ~ r1_tarski(A_266,B_269)
      | r1_tarski(A_266,B_267) ) ),
    inference(resolution,[status(thm)],[c_389,c_2])).

tff(c_2808,plain,(
    ! [A_274,B_275] :
      ( r2_hidden('#skF_1'(A_274,B_275),k4_xboole_0('#skF_3','#skF_4'))
      | ~ r1_tarski(A_274,'#skF_2')
      | r1_tarski(A_274,B_275) ) ),
    inference(resolution,[status(thm)],[c_24,c_2664])).

tff(c_3353,plain,(
    ! [A_298,B_299,B_300] :
      ( r2_hidden('#skF_1'(A_298,B_299),B_300)
      | ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),B_300)
      | ~ r1_tarski(A_298,'#skF_2')
      | r1_tarski(A_298,B_299) ) ),
    inference(resolution,[status(thm)],[c_2808,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3626,plain,(
    ! [B_320,A_321] :
      ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_4'),B_320)
      | ~ r1_tarski(A_321,'#skF_2')
      | r1_tarski(A_321,B_320) ) ),
    inference(resolution,[status(thm)],[c_3353,c_4])).

tff(c_3709,plain,(
    ! [A_322] :
      ( ~ r1_tarski(A_322,'#skF_2')
      | r1_tarski(A_322,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1514,c_3626])).

tff(c_3737,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_3709])).

tff(c_3747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_3737])).

tff(c_3748,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_3776,plain,(
    ! [A_334,C_335,B_336] :
      ( r1_xboole_0(A_334,C_335)
      | ~ r1_xboole_0(B_336,C_335)
      | ~ r1_tarski(A_334,B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3783,plain,(
    ! [A_337,B_338,A_339] :
      ( r1_xboole_0(A_337,B_338)
      | ~ r1_tarski(A_337,k4_xboole_0(A_339,B_338)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3776])).

tff(c_3790,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_3783])).

tff(c_3796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3748,c_3790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.25/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.08  
% 5.25/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.08  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.25/2.08  
% 5.25/2.08  %Foreground sorts:
% 5.25/2.08  
% 5.25/2.08  
% 5.25/2.08  %Background operators:
% 5.25/2.08  
% 5.25/2.08  
% 5.25/2.08  %Foreground operators:
% 5.25/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.25/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.25/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.25/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.25/2.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.25/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.25/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.25/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.25/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.25/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.25/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.25/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.25/2.08  
% 5.70/2.09  tff(f_65, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.70/2.09  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.70/2.09  tff(f_58, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.70/2.09  tff(f_40, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.70/2.09  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.70/2.09  tff(f_44, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.70/2.09  tff(f_56, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 5.70/2.09  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.70/2.09  tff(c_22, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.70/2.09  tff(c_26, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_22])).
% 5.70/2.09  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.70/2.09  tff(c_37, plain, (![A_32, B_33]: (~r2_hidden('#skF_1'(A_32, B_33), B_33) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.70/2.09  tff(c_42, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_37])).
% 5.70/2.09  tff(c_20, plain, (![A_22, B_23]: (r1_xboole_0(k4_xboole_0(A_22, B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.70/2.09  tff(c_163, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k4_xboole_0(A_65, B_66), C_67)=k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.70/2.09  tff(c_193, plain, (![A_65, B_66, C_67]: (r1_xboole_0(k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)), C_67))), inference(superposition, [status(thm), theory('equality')], [c_163, c_20])).
% 5.70/2.09  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.70/2.09  tff(c_88, plain, (![A_46, B_47, C_48]: (r1_tarski(A_46, k2_xboole_0(B_47, C_48)) | ~r1_tarski(k4_xboole_0(A_46, B_47), C_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.70/2.09  tff(c_92, plain, (![A_46, B_47]: (r1_tarski(A_46, k2_xboole_0(B_47, k4_xboole_0(A_46, B_47))))), inference(resolution, [status(thm)], [c_42, c_88])).
% 5.70/2.09  tff(c_95, plain, (![A_49, B_50]: (r1_tarski(A_49, k2_xboole_0(B_50, A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_92])).
% 5.70/2.09  tff(c_102, plain, (![B_9, A_8]: (r1_tarski(k4_xboole_0(B_9, A_8), k2_xboole_0(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_95])).
% 5.70/2.09  tff(c_321, plain, (![A_92, B_93, C_94]: (r1_tarski(A_92, B_93) | ~r1_xboole_0(A_92, C_94) | ~r1_tarski(A_92, k2_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.70/2.09  tff(c_877, plain, (![B_151, A_152]: (r1_tarski(k4_xboole_0(B_151, A_152), A_152) | ~r1_xboole_0(k4_xboole_0(B_151, A_152), B_151))), inference(resolution, [status(thm)], [c_102, c_321])).
% 5.70/2.09  tff(c_1387, plain, (![C_174, B_175]: (r1_tarski(k4_xboole_0(C_174, k2_xboole_0(B_175, C_174)), k2_xboole_0(B_175, C_174)))), inference(resolution, [status(thm)], [c_193, c_877])).
% 5.70/2.09  tff(c_18, plain, (![A_19, B_20, C_21]: (r1_tarski(A_19, B_20) | ~r1_xboole_0(A_19, C_21) | ~r1_tarski(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.70/2.09  tff(c_1395, plain, (![C_174, B_175]: (r1_tarski(k4_xboole_0(C_174, k2_xboole_0(B_175, C_174)), B_175) | ~r1_xboole_0(k4_xboole_0(C_174, k2_xboole_0(B_175, C_174)), C_174))), inference(resolution, [status(thm)], [c_1387, c_18])).
% 5.70/2.09  tff(c_1432, plain, (![C_176, B_177]: (r1_tarski(k4_xboole_0(C_176, k2_xboole_0(B_177, C_176)), B_177))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_1395])).
% 5.70/2.09  tff(c_14, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, k2_xboole_0(B_14, C_15)) | ~r1_tarski(k4_xboole_0(A_13, B_14), C_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.70/2.09  tff(c_181, plain, (![A_65, B_66, C_67, C_15]: (r1_tarski(k4_xboole_0(A_65, B_66), k2_xboole_0(C_67, C_15)) | ~r1_tarski(k4_xboole_0(A_65, k2_xboole_0(B_66, C_67)), C_15))), inference(superposition, [status(thm), theory('equality')], [c_163, c_14])).
% 5.70/2.09  tff(c_1483, plain, (![C_178, B_179]: (r1_tarski(k4_xboole_0(C_178, B_179), k2_xboole_0(C_178, B_179)))), inference(resolution, [status(thm)], [c_1432, c_181])).
% 5.70/2.09  tff(c_1492, plain, (![C_178, B_179]: (r1_tarski(k4_xboole_0(C_178, B_179), C_178) | ~r1_xboole_0(k4_xboole_0(C_178, B_179), B_179))), inference(resolution, [status(thm)], [c_1483, c_18])).
% 5.70/2.09  tff(c_1514, plain, (![C_178, B_179]: (r1_tarski(k4_xboole_0(C_178, B_179), C_178))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1492])).
% 5.70/2.09  tff(c_24, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.70/2.09  tff(c_53, plain, (![C_37, B_38, A_39]: (r2_hidden(C_37, B_38) | ~r2_hidden(C_37, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.70/2.09  tff(c_389, plain, (![A_100, B_101, B_102]: (r2_hidden('#skF_1'(A_100, B_101), B_102) | ~r1_tarski(A_100, B_102) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_6, c_53])).
% 5.70/2.09  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.70/2.09  tff(c_2664, plain, (![A_266, B_267, B_268, B_269]: (r2_hidden('#skF_1'(A_266, B_267), B_268) | ~r1_tarski(B_269, B_268) | ~r1_tarski(A_266, B_269) | r1_tarski(A_266, B_267))), inference(resolution, [status(thm)], [c_389, c_2])).
% 5.70/2.09  tff(c_2808, plain, (![A_274, B_275]: (r2_hidden('#skF_1'(A_274, B_275), k4_xboole_0('#skF_3', '#skF_4')) | ~r1_tarski(A_274, '#skF_2') | r1_tarski(A_274, B_275))), inference(resolution, [status(thm)], [c_24, c_2664])).
% 5.70/2.09  tff(c_3353, plain, (![A_298, B_299, B_300]: (r2_hidden('#skF_1'(A_298, B_299), B_300) | ~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), B_300) | ~r1_tarski(A_298, '#skF_2') | r1_tarski(A_298, B_299))), inference(resolution, [status(thm)], [c_2808, c_2])).
% 5.70/2.09  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.70/2.09  tff(c_3626, plain, (![B_320, A_321]: (~r1_tarski(k4_xboole_0('#skF_3', '#skF_4'), B_320) | ~r1_tarski(A_321, '#skF_2') | r1_tarski(A_321, B_320))), inference(resolution, [status(thm)], [c_3353, c_4])).
% 5.70/2.09  tff(c_3709, plain, (![A_322]: (~r1_tarski(A_322, '#skF_2') | r1_tarski(A_322, '#skF_3'))), inference(resolution, [status(thm)], [c_1514, c_3626])).
% 5.70/2.09  tff(c_3737, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_3709])).
% 5.70/2.09  tff(c_3747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_3737])).
% 5.70/2.09  tff(c_3748, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 5.70/2.09  tff(c_3776, plain, (![A_334, C_335, B_336]: (r1_xboole_0(A_334, C_335) | ~r1_xboole_0(B_336, C_335) | ~r1_tarski(A_334, B_336))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.70/2.09  tff(c_3783, plain, (![A_337, B_338, A_339]: (r1_xboole_0(A_337, B_338) | ~r1_tarski(A_337, k4_xboole_0(A_339, B_338)))), inference(resolution, [status(thm)], [c_20, c_3776])).
% 5.70/2.09  tff(c_3790, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_3783])).
% 5.70/2.09  tff(c_3796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3748, c_3790])).
% 5.70/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.09  
% 5.70/2.09  Inference rules
% 5.70/2.09  ----------------------
% 5.70/2.09  #Ref     : 0
% 5.70/2.09  #Sup     : 947
% 5.70/2.09  #Fact    : 0
% 5.70/2.09  #Define  : 0
% 5.70/2.09  #Split   : 6
% 5.70/2.09  #Chain   : 0
% 5.70/2.09  #Close   : 0
% 5.70/2.09  
% 5.70/2.09  Ordering : KBO
% 5.70/2.09  
% 5.70/2.09  Simplification rules
% 5.70/2.09  ----------------------
% 5.70/2.09  #Subsume      : 45
% 5.70/2.09  #Demod        : 358
% 5.70/2.09  #Tautology    : 141
% 5.70/2.09  #SimpNegUnit  : 2
% 5.70/2.09  #BackRed      : 0
% 5.70/2.09  
% 5.70/2.09  #Partial instantiations: 0
% 5.70/2.09  #Strategies tried      : 1
% 5.70/2.09  
% 5.70/2.09  Timing (in seconds)
% 5.70/2.09  ----------------------
% 5.70/2.10  Preprocessing        : 0.28
% 5.70/2.10  Parsing              : 0.16
% 5.70/2.10  CNF conversion       : 0.02
% 5.70/2.10  Main loop            : 1.03
% 5.70/2.10  Inferencing          : 0.33
% 5.70/2.10  Reduction            : 0.34
% 5.70/2.10  Demodulation         : 0.26
% 5.70/2.10  BG Simplification    : 0.03
% 5.70/2.10  Subsumption          : 0.25
% 5.70/2.10  Abstraction          : 0.04
% 5.70/2.10  MUC search           : 0.00
% 5.70/2.10  Cooper               : 0.00
% 5.70/2.10  Total                : 1.35
% 5.70/2.10  Index Insertion      : 0.00
% 5.70/2.10  Index Deletion       : 0.00
% 5.70/2.10  Index Matching       : 0.00
% 5.70/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
