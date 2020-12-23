%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:19 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :   52 (  79 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   19
%              Number of atoms          :   82 ( 166 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

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

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_11,C_13,B_12] :
      ( ~ r1_xboole_0(A_11,C_13)
      | ~ r1_xboole_0(A_11,B_12)
      | r1_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_60,plain,(
    ! [A_34,B_35] : k2_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,C_13)
      | ~ r1_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,(
    ! [A_11,B_35,A_34] :
      ( r1_xboole_0(A_11,k4_xboole_0(B_35,A_34))
      | ~ r1_xboole_0(A_11,k2_xboole_0(A_34,B_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_14])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,B_37)
      | ~ r2_hidden(C_38,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_106,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,k4_xboole_0(A_42,B_41)) ) ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_891,plain,(
    ! [A_141,A_142,B_143] :
      ( ~ r2_hidden('#skF_1'(A_141,k4_xboole_0(A_142,B_143)),B_143)
      | r1_xboole_0(A_141,k4_xboole_0(A_142,B_143)) ) ),
    inference(resolution,[status(thm)],[c_4,c_106])).

tff(c_901,plain,(
    ! [A_144,A_145] : r1_xboole_0(A_144,k4_xboole_0(A_145,A_144)) ),
    inference(resolution,[status(thm)],[c_6,c_891])).

tff(c_216,plain,(
    ! [A_56,C_57,B_58] :
      ( ~ r1_xboole_0(A_56,C_57)
      | ~ r1_xboole_0(A_56,B_58)
      | r1_xboole_0(A_56,k2_xboole_0(B_58,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_227,plain,(
    ! [A_56,B_7,A_6] :
      ( ~ r1_xboole_0(A_56,k4_xboole_0(B_7,A_6))
      | ~ r1_xboole_0(A_56,A_6)
      | r1_xboole_0(A_56,k2_xboole_0(A_6,B_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_216])).

tff(c_930,plain,(
    ! [A_149,A_150] :
      ( ~ r1_xboole_0(A_149,A_149)
      | r1_xboole_0(A_149,k2_xboole_0(A_149,A_150)) ) ),
    inference(resolution,[status(thm)],[c_901,c_227])).

tff(c_948,plain,(
    ! [A_151,A_152] :
      ( r1_xboole_0(A_151,A_152)
      | ~ r1_xboole_0(A_151,A_151) ) ),
    inference(resolution,[status(thm)],[c_930,c_14])).

tff(c_1612,plain,(
    ! [B_236,A_237,A_238] :
      ( r1_xboole_0(k4_xboole_0(B_236,A_237),A_238)
      | ~ r1_xboole_0(k4_xboole_0(B_236,A_237),k2_xboole_0(A_237,B_236)) ) ),
    inference(resolution,[status(thm)],[c_69,c_948])).

tff(c_1622,plain,(
    ! [C_13,B_12,A_238] :
      ( r1_xboole_0(k4_xboole_0(C_13,B_12),A_238)
      | ~ r1_xboole_0(k4_xboole_0(C_13,B_12),C_13)
      | ~ r1_xboole_0(k4_xboole_0(C_13,B_12),B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_1612])).

tff(c_1636,plain,(
    ! [C_239,B_240,A_241] :
      ( r1_xboole_0(k4_xboole_0(C_239,B_240),A_241)
      | ~ r1_xboole_0(k4_xboole_0(C_239,B_240),C_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1622])).

tff(c_1717,plain,(
    ! [B_242,A_243] : r1_xboole_0(k4_xboole_0(B_242,B_242),A_243) ),
    inference(resolution,[status(thm)],[c_18,c_1636])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1769,plain,(
    ! [C_244,A_245,B_246] :
      ( ~ r2_hidden(C_244,A_245)
      | ~ r2_hidden(C_244,k4_xboole_0(B_246,B_246)) ) ),
    inference(resolution,[status(thm)],[c_1717,c_2])).

tff(c_2082,plain,(
    ! [A_273,B_274,B_275] :
      ( ~ r2_hidden('#skF_1'(A_273,B_274),k4_xboole_0(B_275,B_275))
      | r1_xboole_0(A_273,B_274) ) ),
    inference(resolution,[status(thm)],[c_4,c_1769])).

tff(c_2103,plain,(
    ! [A_276,B_277] : r1_xboole_0(A_276,k4_xboole_0(B_277,B_277)) ),
    inference(resolution,[status(thm)],[c_4,c_2082])).

tff(c_2122,plain,(
    ! [A_276,A_8,B_9] : r1_xboole_0(A_276,k4_xboole_0(A_8,k2_xboole_0(B_9,k4_xboole_0(A_8,B_9)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2103])).

tff(c_2129,plain,(
    ! [A_276,A_8,B_9] : r1_xboole_0(A_276,k4_xboole_0(A_8,k2_xboole_0(B_9,A_8))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2122])).

tff(c_718,plain,(
    ! [A_127,B_128,A_129] :
      ( ~ r1_xboole_0(A_127,k4_xboole_0(B_128,A_129))
      | ~ r1_xboole_0(A_127,A_129)
      | r1_xboole_0(A_127,k2_xboole_0(A_129,B_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_216])).

tff(c_6643,plain,(
    ! [A_567,A_568,B_569,C_570] :
      ( ~ r1_xboole_0(A_567,k4_xboole_0(A_568,k2_xboole_0(B_569,C_570)))
      | ~ r1_xboole_0(A_567,C_570)
      | r1_xboole_0(A_567,k2_xboole_0(C_570,k4_xboole_0(A_568,B_569))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_718])).

tff(c_7059,plain,(
    ! [A_574,A_575,B_576] :
      ( ~ r1_xboole_0(A_574,A_575)
      | r1_xboole_0(A_574,k2_xboole_0(A_575,k4_xboole_0(A_575,B_576))) ) ),
    inference(resolution,[status(thm)],[c_2129,c_6643])).

tff(c_7126,plain,(
    ! [A_577,A_578,B_579] :
      ( r1_xboole_0(A_577,k4_xboole_0(A_578,B_579))
      | ~ r1_xboole_0(A_577,A_578) ) ),
    inference(resolution,[status(thm)],[c_7059,c_14])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7147,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_7126,c_20])).

tff(c_7170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.40  
% 6.93/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.40  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.93/2.40  
% 6.93/2.40  %Foreground sorts:
% 6.93/2.40  
% 6.93/2.40  
% 6.93/2.40  %Background operators:
% 6.93/2.40  
% 6.93/2.40  
% 6.93/2.40  %Foreground operators:
% 6.93/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.93/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.93/2.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.93/2.40  tff('#skF_2', type, '#skF_2': $i).
% 6.93/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.93/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.40  tff('#skF_4', type, '#skF_4': $i).
% 6.93/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.93/2.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.93/2.40  
% 6.93/2.41  tff(f_70, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 6.93/2.41  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.93/2.41  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.93/2.41  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.93/2.41  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.93/2.41  tff(f_63, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.93/2.41  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.93/2.41  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.93/2.41  tff(c_10, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.93/2.41  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.41  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.93/2.41  tff(c_12, plain, (![A_11, C_13, B_12]: (~r1_xboole_0(A_11, C_13) | ~r1_xboole_0(A_11, B_12) | r1_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.93/2.41  tff(c_60, plain, (![A_34, B_35]: (k2_xboole_0(A_34, k4_xboole_0(B_35, A_34))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.93/2.41  tff(c_14, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, C_13) | ~r1_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.93/2.41  tff(c_69, plain, (![A_11, B_35, A_34]: (r1_xboole_0(A_11, k4_xboole_0(B_35, A_34)) | ~r1_xboole_0(A_11, k2_xboole_0(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_14])).
% 6.93/2.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.41  tff(c_82, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, B_37) | ~r2_hidden(C_38, A_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.41  tff(c_106, plain, (![C_40, B_41, A_42]: (~r2_hidden(C_40, B_41) | ~r2_hidden(C_40, k4_xboole_0(A_42, B_41)))), inference(resolution, [status(thm)], [c_18, c_82])).
% 6.93/2.41  tff(c_891, plain, (![A_141, A_142, B_143]: (~r2_hidden('#skF_1'(A_141, k4_xboole_0(A_142, B_143)), B_143) | r1_xboole_0(A_141, k4_xboole_0(A_142, B_143)))), inference(resolution, [status(thm)], [c_4, c_106])).
% 6.93/2.41  tff(c_901, plain, (![A_144, A_145]: (r1_xboole_0(A_144, k4_xboole_0(A_145, A_144)))), inference(resolution, [status(thm)], [c_6, c_891])).
% 6.93/2.41  tff(c_216, plain, (![A_56, C_57, B_58]: (~r1_xboole_0(A_56, C_57) | ~r1_xboole_0(A_56, B_58) | r1_xboole_0(A_56, k2_xboole_0(B_58, C_57)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.93/2.41  tff(c_227, plain, (![A_56, B_7, A_6]: (~r1_xboole_0(A_56, k4_xboole_0(B_7, A_6)) | ~r1_xboole_0(A_56, A_6) | r1_xboole_0(A_56, k2_xboole_0(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_216])).
% 6.93/2.41  tff(c_930, plain, (![A_149, A_150]: (~r1_xboole_0(A_149, A_149) | r1_xboole_0(A_149, k2_xboole_0(A_149, A_150)))), inference(resolution, [status(thm)], [c_901, c_227])).
% 6.93/2.41  tff(c_948, plain, (![A_151, A_152]: (r1_xboole_0(A_151, A_152) | ~r1_xboole_0(A_151, A_151))), inference(resolution, [status(thm)], [c_930, c_14])).
% 6.93/2.41  tff(c_1612, plain, (![B_236, A_237, A_238]: (r1_xboole_0(k4_xboole_0(B_236, A_237), A_238) | ~r1_xboole_0(k4_xboole_0(B_236, A_237), k2_xboole_0(A_237, B_236)))), inference(resolution, [status(thm)], [c_69, c_948])).
% 6.93/2.41  tff(c_1622, plain, (![C_13, B_12, A_238]: (r1_xboole_0(k4_xboole_0(C_13, B_12), A_238) | ~r1_xboole_0(k4_xboole_0(C_13, B_12), C_13) | ~r1_xboole_0(k4_xboole_0(C_13, B_12), B_12))), inference(resolution, [status(thm)], [c_12, c_1612])).
% 6.93/2.41  tff(c_1636, plain, (![C_239, B_240, A_241]: (r1_xboole_0(k4_xboole_0(C_239, B_240), A_241) | ~r1_xboole_0(k4_xboole_0(C_239, B_240), C_239))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1622])).
% 6.93/2.41  tff(c_1717, plain, (![B_242, A_243]: (r1_xboole_0(k4_xboole_0(B_242, B_242), A_243))), inference(resolution, [status(thm)], [c_18, c_1636])).
% 6.93/2.41  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.41  tff(c_1769, plain, (![C_244, A_245, B_246]: (~r2_hidden(C_244, A_245) | ~r2_hidden(C_244, k4_xboole_0(B_246, B_246)))), inference(resolution, [status(thm)], [c_1717, c_2])).
% 6.93/2.41  tff(c_2082, plain, (![A_273, B_274, B_275]: (~r2_hidden('#skF_1'(A_273, B_274), k4_xboole_0(B_275, B_275)) | r1_xboole_0(A_273, B_274))), inference(resolution, [status(thm)], [c_4, c_1769])).
% 6.93/2.41  tff(c_2103, plain, (![A_276, B_277]: (r1_xboole_0(A_276, k4_xboole_0(B_277, B_277)))), inference(resolution, [status(thm)], [c_4, c_2082])).
% 6.93/2.41  tff(c_2122, plain, (![A_276, A_8, B_9]: (r1_xboole_0(A_276, k4_xboole_0(A_8, k2_xboole_0(B_9, k4_xboole_0(A_8, B_9)))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2103])).
% 6.93/2.41  tff(c_2129, plain, (![A_276, A_8, B_9]: (r1_xboole_0(A_276, k4_xboole_0(A_8, k2_xboole_0(B_9, A_8))))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2122])).
% 6.93/2.41  tff(c_718, plain, (![A_127, B_128, A_129]: (~r1_xboole_0(A_127, k4_xboole_0(B_128, A_129)) | ~r1_xboole_0(A_127, A_129) | r1_xboole_0(A_127, k2_xboole_0(A_129, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_216])).
% 6.93/2.41  tff(c_6643, plain, (![A_567, A_568, B_569, C_570]: (~r1_xboole_0(A_567, k4_xboole_0(A_568, k2_xboole_0(B_569, C_570))) | ~r1_xboole_0(A_567, C_570) | r1_xboole_0(A_567, k2_xboole_0(C_570, k4_xboole_0(A_568, B_569))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_718])).
% 6.93/2.41  tff(c_7059, plain, (![A_574, A_575, B_576]: (~r1_xboole_0(A_574, A_575) | r1_xboole_0(A_574, k2_xboole_0(A_575, k4_xboole_0(A_575, B_576))))), inference(resolution, [status(thm)], [c_2129, c_6643])).
% 6.93/2.41  tff(c_7126, plain, (![A_577, A_578, B_579]: (r1_xboole_0(A_577, k4_xboole_0(A_578, B_579)) | ~r1_xboole_0(A_577, A_578))), inference(resolution, [status(thm)], [c_7059, c_14])).
% 6.93/2.41  tff(c_20, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.93/2.41  tff(c_7147, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_7126, c_20])).
% 6.93/2.41  tff(c_7170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_7147])).
% 6.93/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.41  
% 6.93/2.41  Inference rules
% 6.93/2.41  ----------------------
% 6.93/2.41  #Ref     : 0
% 6.93/2.41  #Sup     : 1691
% 6.93/2.41  #Fact    : 0
% 6.93/2.41  #Define  : 0
% 6.93/2.41  #Split   : 0
% 6.93/2.41  #Chain   : 0
% 6.93/2.41  #Close   : 0
% 6.93/2.41  
% 6.93/2.41  Ordering : KBO
% 6.93/2.41  
% 6.93/2.41  Simplification rules
% 6.93/2.41  ----------------------
% 6.93/2.41  #Subsume      : 113
% 6.93/2.41  #Demod        : 1146
% 6.93/2.41  #Tautology    : 521
% 6.93/2.41  #SimpNegUnit  : 0
% 6.93/2.41  #BackRed      : 13
% 6.93/2.41  
% 6.93/2.41  #Partial instantiations: 0
% 6.93/2.41  #Strategies tried      : 1
% 6.93/2.41  
% 6.93/2.41  Timing (in seconds)
% 6.93/2.41  ----------------------
% 6.93/2.42  Preprocessing        : 0.27
% 6.93/2.42  Parsing              : 0.16
% 6.93/2.42  CNF conversion       : 0.02
% 6.93/2.42  Main loop            : 1.42
% 6.93/2.42  Inferencing          : 0.41
% 6.93/2.42  Reduction            : 0.55
% 6.93/2.42  Demodulation         : 0.46
% 6.93/2.42  BG Simplification    : 0.04
% 6.93/2.42  Subsumption          : 0.33
% 6.93/2.42  Abstraction          : 0.05
% 6.93/2.42  MUC search           : 0.00
% 6.93/2.42  Cooper               : 0.00
% 6.93/2.42  Total                : 1.72
% 6.93/2.42  Index Insertion      : 0.00
% 6.93/2.42  Index Deletion       : 0.00
% 6.93/2.42  Index Matching       : 0.00
% 6.93/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
