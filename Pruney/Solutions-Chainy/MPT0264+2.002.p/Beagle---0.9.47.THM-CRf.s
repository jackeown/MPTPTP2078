%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:21 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   49 (  51 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  56 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_49,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_3'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_114,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_150,plain,(
    k3_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_3')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_114])).

tff(c_18,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_476,plain,(
    ! [A_77,C_78,B_79] :
      ( r2_hidden(A_77,C_78)
      | ~ r2_hidden(A_77,B_79)
      | r2_hidden(A_77,k5_xboole_0(B_79,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_998,plain,(
    ! [A_111,A_112,B_113] :
      ( r2_hidden(A_111,k3_xboole_0(A_112,B_113))
      | ~ r2_hidden(A_111,A_112)
      | r2_hidden(A_111,k4_xboole_0(A_112,B_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_476])).

tff(c_20,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_62,plain,(
    ! [B_31,A_32] :
      ( r1_xboole_0(B_31,A_32)
      | ~ r1_xboole_0(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [B_13,A_12] : r1_xboole_0(B_13,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_313,plain,(
    ! [A_55,C_56,B_57] :
      ( ~ r2_hidden(A_55,C_56)
      | ~ r1_xboole_0(k2_tarski(A_55,B_57),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_327,plain,(
    ! [A_55,A_12,B_57] : ~ r2_hidden(A_55,k4_xboole_0(A_12,k2_tarski(A_55,B_57))) ),
    inference(resolution,[status(thm)],[c_65,c_313])).

tff(c_1079,plain,(
    ! [A_119,A_120,B_121] :
      ( r2_hidden(A_119,k3_xboole_0(A_120,k2_tarski(A_119,B_121)))
      | ~ r2_hidden(A_119,A_120) ) ),
    inference(resolution,[status(thm)],[c_998,c_327])).

tff(c_1082,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_1079])).

tff(c_1101,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1082])).

tff(c_26,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1104,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1101,c_26])).

tff(c_1108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:20:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.46  
% 3.02/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.46  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.15/1.46  
% 3.15/1.46  %Foreground sorts:
% 3.15/1.46  
% 3.15/1.46  
% 3.15/1.46  %Background operators:
% 3.15/1.46  
% 3.15/1.46  
% 3.15/1.46  %Foreground operators:
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.46  
% 3.15/1.47  tff(f_71, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 3.15/1.47  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.15/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.47  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.47  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.15/1.47  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.15/1.47  tff(f_44, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 3.15/1.47  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.15/1.47  tff(f_62, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.15/1.47  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.15/1.47  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.47  tff(c_46, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.47  tff(c_24, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.47  tff(c_48, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.47  tff(c_49, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_3'), '#skF_5')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_48])).
% 3.15/1.47  tff(c_114, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)=k3_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.47  tff(c_150, plain, (k3_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_3'))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_49, c_114])).
% 3.15/1.47  tff(c_18, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.47  tff(c_476, plain, (![A_77, C_78, B_79]: (r2_hidden(A_77, C_78) | ~r2_hidden(A_77, B_79) | r2_hidden(A_77, k5_xboole_0(B_79, C_78)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.47  tff(c_998, plain, (![A_111, A_112, B_113]: (r2_hidden(A_111, k3_xboole_0(A_112, B_113)) | ~r2_hidden(A_111, A_112) | r2_hidden(A_111, k4_xboole_0(A_112, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_476])).
% 3.15/1.47  tff(c_20, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.47  tff(c_22, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, k3_xboole_0(A_12, B_13)), B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.47  tff(c_50, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 3.15/1.47  tff(c_62, plain, (![B_31, A_32]: (r1_xboole_0(B_31, A_32) | ~r1_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.47  tff(c_65, plain, (![B_13, A_12]: (r1_xboole_0(B_13, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_50, c_62])).
% 3.15/1.47  tff(c_313, plain, (![A_55, C_56, B_57]: (~r2_hidden(A_55, C_56) | ~r1_xboole_0(k2_tarski(A_55, B_57), C_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.47  tff(c_327, plain, (![A_55, A_12, B_57]: (~r2_hidden(A_55, k4_xboole_0(A_12, k2_tarski(A_55, B_57))))), inference(resolution, [status(thm)], [c_65, c_313])).
% 3.15/1.47  tff(c_1079, plain, (![A_119, A_120, B_121]: (r2_hidden(A_119, k3_xboole_0(A_120, k2_tarski(A_119, B_121))) | ~r2_hidden(A_119, A_120))), inference(resolution, [status(thm)], [c_998, c_327])).
% 3.15/1.47  tff(c_1082, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3')) | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_150, c_1079])).
% 3.15/1.47  tff(c_1101, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1082])).
% 3.15/1.47  tff(c_26, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.15/1.47  tff(c_1104, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1101, c_26])).
% 3.15/1.47  tff(c_1108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1104])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 265
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 0
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.48  #Subsume      : 19
% 3.15/1.48  #Demod        : 160
% 3.15/1.48  #Tautology    : 153
% 3.15/1.48  #SimpNegUnit  : 1
% 3.15/1.48  #BackRed      : 2
% 3.15/1.48  
% 3.15/1.48  #Partial instantiations: 0
% 3.15/1.48  #Strategies tried      : 1
% 3.15/1.48  
% 3.15/1.48  Timing (in seconds)
% 3.15/1.48  ----------------------
% 3.15/1.48  Preprocessing        : 0.30
% 3.15/1.48  Parsing              : 0.16
% 3.15/1.48  CNF conversion       : 0.02
% 3.15/1.48  Main loop            : 0.42
% 3.15/1.48  Inferencing          : 0.13
% 3.15/1.48  Reduction            : 0.18
% 3.15/1.48  Demodulation         : 0.14
% 3.15/1.48  BG Simplification    : 0.02
% 3.15/1.48  Subsumption          : 0.07
% 3.15/1.48  Abstraction          : 0.02
% 3.15/1.48  MUC search           : 0.00
% 3.15/1.48  Cooper               : 0.00
% 3.15/1.48  Total                : 0.75
% 3.15/1.48  Index Insertion      : 0.00
% 3.15/1.48  Index Deletion       : 0.00
% 3.15/1.48  Index Matching       : 0.00
% 3.15/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
