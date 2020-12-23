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
% DateTime   : Thu Dec  3 09:44:18 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :   49 (  62 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  75 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_54,axiom,(
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

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(c_34,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_350,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k4_xboole_0(A_58,B_59),C_60) = k4_xboole_0(A_58,k2_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_48])).

tff(c_366,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k2_xboole_0(B_59,k4_xboole_0(A_58,B_59))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_55])).

tff(c_435,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k2_xboole_0(B_63,A_62)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_366])).

tff(c_924,plain,(
    ! [A_85,B_86] : k2_xboole_0(k3_xboole_0(A_85,k2_xboole_0(B_86,A_85)),k1_xboole_0) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_34])).

tff(c_67,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_79,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = k2_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_67])).

tff(c_86,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_79])).

tff(c_1002,plain,(
    ! [A_87,B_88] : k3_xboole_0(A_87,k2_xboole_0(B_88,A_87)) = A_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_86])).

tff(c_1054,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),A_21) = k4_xboole_0(A_21,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1002])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_198,plain,(
    ! [D_42,B_43,A_44] :
      ( r2_hidden(D_42,B_43)
      | ~ r2_hidden(D_42,k3_xboole_0(A_44,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6589,plain,(
    ! [A_246,A_247,B_248] :
      ( r2_hidden('#skF_3'(A_246,k3_xboole_0(A_247,B_248)),B_248)
      | r1_xboole_0(A_246,k3_xboole_0(A_247,B_248)) ) ),
    inference(resolution,[status(thm)],[c_24,c_198])).

tff(c_38,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_318,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,B_53)
      | ~ r2_hidden(C_54,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_321,plain,(
    ! [C_54] :
      ( ~ r2_hidden(C_54,'#skF_5')
      | ~ r2_hidden(C_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_318])).

tff(c_6754,plain,(
    ! [A_252,A_253] :
      ( ~ r2_hidden('#skF_3'(A_252,k3_xboole_0(A_253,'#skF_5')),'#skF_4')
      | r1_xboole_0(A_252,k3_xboole_0(A_253,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6589,c_321])).

tff(c_6799,plain,(
    ! [A_255] : r1_xboole_0('#skF_4',k3_xboole_0(A_255,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_26,c_6754])).

tff(c_6805,plain,(
    ! [B_22] : r1_xboole_0('#skF_4',k4_xboole_0('#skF_5',B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_6799])).

tff(c_36,plain,(
    ~ r1_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6805,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.07  
% 5.09/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.07  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.09/2.07  
% 5.09/2.07  %Foreground sorts:
% 5.09/2.07  
% 5.09/2.07  
% 5.09/2.07  %Background operators:
% 5.09/2.07  
% 5.09/2.07  
% 5.09/2.07  %Foreground operators:
% 5.09/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.09/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.09/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.09/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.09/2.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.09/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.09/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.09/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.09/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.09/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.09/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.09/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.09/2.07  
% 5.09/2.08  tff(f_62, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.09/2.08  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.09/2.08  tff(f_58, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.09/2.08  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.09/2.08  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.09/2.08  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.09/2.08  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.09/2.08  tff(f_67, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 5.09/2.08  tff(c_34, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.09/2.08  tff(c_28, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.09/2.08  tff(c_350, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k4_xboole_0(A_58, B_59), C_60)=k4_xboole_0(A_58, k2_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.09/2.08  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.09/2.08  tff(c_48, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.09/2.08  tff(c_55, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_48])).
% 5.09/2.08  tff(c_366, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k2_xboole_0(B_59, k4_xboole_0(A_58, B_59)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_350, c_55])).
% 5.09/2.08  tff(c_435, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k2_xboole_0(B_63, A_62))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_366])).
% 5.09/2.08  tff(c_924, plain, (![A_85, B_86]: (k2_xboole_0(k3_xboole_0(A_85, k2_xboole_0(B_86, A_85)), k1_xboole_0)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_435, c_34])).
% 5.09/2.08  tff(c_67, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.09/2.08  tff(c_79, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=k2_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_55, c_67])).
% 5.09/2.08  tff(c_86, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_79])).
% 5.09/2.08  tff(c_1002, plain, (![A_87, B_88]: (k3_xboole_0(A_87, k2_xboole_0(B_88, A_87))=A_87)), inference(superposition, [status(thm), theory('equality')], [c_924, c_86])).
% 5.09/2.08  tff(c_1054, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), A_21)=k4_xboole_0(A_21, B_22))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1002])).
% 5.09/2.08  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.09/2.08  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.09/2.08  tff(c_198, plain, (![D_42, B_43, A_44]: (r2_hidden(D_42, B_43) | ~r2_hidden(D_42, k3_xboole_0(A_44, B_43)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.09/2.08  tff(c_6589, plain, (![A_246, A_247, B_248]: (r2_hidden('#skF_3'(A_246, k3_xboole_0(A_247, B_248)), B_248) | r1_xboole_0(A_246, k3_xboole_0(A_247, B_248)))), inference(resolution, [status(thm)], [c_24, c_198])).
% 5.09/2.08  tff(c_38, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.09/2.08  tff(c_318, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, B_53) | ~r2_hidden(C_54, A_52))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.09/2.08  tff(c_321, plain, (![C_54]: (~r2_hidden(C_54, '#skF_5') | ~r2_hidden(C_54, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_318])).
% 5.09/2.08  tff(c_6754, plain, (![A_252, A_253]: (~r2_hidden('#skF_3'(A_252, k3_xboole_0(A_253, '#skF_5')), '#skF_4') | r1_xboole_0(A_252, k3_xboole_0(A_253, '#skF_5')))), inference(resolution, [status(thm)], [c_6589, c_321])).
% 5.09/2.08  tff(c_6799, plain, (![A_255]: (r1_xboole_0('#skF_4', k3_xboole_0(A_255, '#skF_5')))), inference(resolution, [status(thm)], [c_26, c_6754])).
% 5.09/2.08  tff(c_6805, plain, (![B_22]: (r1_xboole_0('#skF_4', k4_xboole_0('#skF_5', B_22)))), inference(superposition, [status(thm), theory('equality')], [c_1054, c_6799])).
% 5.09/2.08  tff(c_36, plain, (~r1_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.09/2.08  tff(c_6823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6805, c_36])).
% 5.09/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.08  
% 5.09/2.08  Inference rules
% 5.09/2.08  ----------------------
% 5.09/2.08  #Ref     : 0
% 5.09/2.08  #Sup     : 1644
% 5.09/2.08  #Fact    : 0
% 5.09/2.08  #Define  : 0
% 5.09/2.08  #Split   : 0
% 5.09/2.08  #Chain   : 0
% 5.09/2.08  #Close   : 0
% 5.09/2.08  
% 5.09/2.08  Ordering : KBO
% 5.09/2.08  
% 5.09/2.08  Simplification rules
% 5.09/2.08  ----------------------
% 5.09/2.08  #Subsume      : 89
% 5.09/2.08  #Demod        : 1307
% 5.09/2.08  #Tautology    : 1089
% 5.09/2.08  #SimpNegUnit  : 0
% 5.09/2.08  #BackRed      : 5
% 5.09/2.08  
% 5.09/2.08  #Partial instantiations: 0
% 5.09/2.08  #Strategies tried      : 1
% 5.09/2.08  
% 5.09/2.08  Timing (in seconds)
% 5.09/2.08  ----------------------
% 5.09/2.09  Preprocessing        : 0.29
% 5.09/2.09  Parsing              : 0.15
% 5.09/2.09  CNF conversion       : 0.02
% 5.18/2.09  Main loop            : 0.92
% 5.18/2.09  Inferencing          : 0.32
% 5.18/2.09  Reduction            : 0.35
% 5.18/2.09  Demodulation         : 0.27
% 5.18/2.09  BG Simplification    : 0.03
% 5.18/2.09  Subsumption          : 0.15
% 5.18/2.09  Abstraction          : 0.05
% 5.18/2.09  MUC search           : 0.00
% 5.18/2.09  Cooper               : 0.00
% 5.18/2.09  Total                : 1.24
% 5.18/2.09  Index Insertion      : 0.00
% 5.18/2.09  Index Deletion       : 0.00
% 5.18/2.09  Index Matching       : 0.00
% 5.18/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
