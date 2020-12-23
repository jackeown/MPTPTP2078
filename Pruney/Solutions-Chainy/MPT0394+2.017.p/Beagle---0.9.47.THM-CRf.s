%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:23 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  85 expanded)
%              Number of equality atoms :   40 (  60 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_34,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_120,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_138,plain,(
    ! [B_51,A_52] : r2_hidden(B_51,k2_tarski(A_52,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_10])).

tff(c_141,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_138])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(A_47,B_48)
      | k3_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_21,B_22] :
      ( ~ r2_hidden(A_21,B_22)
      | ~ r1_xboole_0(k1_tarski(A_21),B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_158,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden(A_59,B_60)
      | k3_xboole_0(k1_tarski(A_59),B_60) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_40])).

tff(c_162,plain,(
    ! [A_59] :
      ( ~ r2_hidden(A_59,k1_tarski(A_59))
      | k1_tarski(A_59) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_164,plain,(
    ! [A_59] : k1_tarski(A_59) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_162])).

tff(c_46,plain,(
    ! [A_27] : k1_setfam_1(k1_tarski(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_165,plain,(
    ! [A_61,B_62,C_63] : k2_xboole_0(k2_tarski(A_61,B_62),k1_tarski(C_63)) = k1_enumset1(A_61,B_62,C_63) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_174,plain,(
    ! [A_15,C_63] : k2_xboole_0(k1_tarski(A_15),k1_tarski(C_63)) = k1_enumset1(A_15,A_15,C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_165])).

tff(c_177,plain,(
    ! [A_15,C_63] : k2_xboole_0(k1_tarski(A_15),k1_tarski(C_63)) = k2_tarski(A_15,C_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_174])).

tff(c_227,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(k1_setfam_1(A_72),k1_setfam_1(B_73)) = k1_setfam_1(k2_xboole_0(A_72,B_73))
      | k1_xboole_0 = B_73
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_244,plain,(
    ! [A_27,B_73] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_27),B_73)) = k3_xboole_0(A_27,k1_setfam_1(B_73))
      | k1_xboole_0 = B_73
      | k1_tarski(A_27) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_227])).

tff(c_320,plain,(
    ! [A_85,B_86] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_85),B_86)) = k3_xboole_0(A_85,k1_setfam_1(B_86))
      | k1_xboole_0 = B_86 ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_244])).

tff(c_343,plain,(
    ! [A_15,C_63] :
      ( k3_xboole_0(A_15,k1_setfam_1(k1_tarski(C_63))) = k1_setfam_1(k2_tarski(A_15,C_63))
      | k1_tarski(C_63) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_320])).

tff(c_354,plain,(
    ! [A_15,C_63] :
      ( k1_setfam_1(k2_tarski(A_15,C_63)) = k3_xboole_0(A_15,C_63)
      | k1_tarski(C_63) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_343])).

tff(c_355,plain,(
    ! [A_15,C_63] : k1_setfam_1(k2_tarski(A_15,C_63)) = k3_xboole_0(A_15,C_63) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_354])).

tff(c_48,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.26  
% 2.07/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.26  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.07/1.26  
% 2.07/1.26  %Foreground sorts:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Background operators:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Foreground operators:
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.07/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.07/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.07/1.26  
% 2.07/1.27  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.27  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.07/1.27  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.07/1.27  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.07/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.07/1.27  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.07/1.27  tff(f_73, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.07/1.27  tff(f_48, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.07/1.27  tff(f_71, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.07/1.27  tff(f_76, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.07/1.27  tff(c_34, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.27  tff(c_120, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.27  tff(c_10, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.27  tff(c_138, plain, (![B_51, A_52]: (r2_hidden(B_51, k2_tarski(A_52, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_10])).
% 2.07/1.27  tff(c_141, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_138])).
% 2.07/1.27  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.27  tff(c_110, plain, (![A_47, B_48]: (r1_xboole_0(A_47, B_48) | k3_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.27  tff(c_40, plain, (![A_21, B_22]: (~r2_hidden(A_21, B_22) | ~r1_xboole_0(k1_tarski(A_21), B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.27  tff(c_158, plain, (![A_59, B_60]: (~r2_hidden(A_59, B_60) | k3_xboole_0(k1_tarski(A_59), B_60)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_40])).
% 2.07/1.27  tff(c_162, plain, (![A_59]: (~r2_hidden(A_59, k1_tarski(A_59)) | k1_tarski(A_59)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_158])).
% 2.07/1.27  tff(c_164, plain, (![A_59]: (k1_tarski(A_59)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_162])).
% 2.07/1.27  tff(c_46, plain, (![A_27]: (k1_setfam_1(k1_tarski(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.07/1.27  tff(c_36, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.27  tff(c_165, plain, (![A_61, B_62, C_63]: (k2_xboole_0(k2_tarski(A_61, B_62), k1_tarski(C_63))=k1_enumset1(A_61, B_62, C_63))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.27  tff(c_174, plain, (![A_15, C_63]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(C_63))=k1_enumset1(A_15, A_15, C_63))), inference(superposition, [status(thm), theory('equality')], [c_34, c_165])).
% 2.07/1.27  tff(c_177, plain, (![A_15, C_63]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(C_63))=k2_tarski(A_15, C_63))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_174])).
% 2.07/1.27  tff(c_227, plain, (![A_72, B_73]: (k3_xboole_0(k1_setfam_1(A_72), k1_setfam_1(B_73))=k1_setfam_1(k2_xboole_0(A_72, B_73)) | k1_xboole_0=B_73 | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.27  tff(c_244, plain, (![A_27, B_73]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_27), B_73))=k3_xboole_0(A_27, k1_setfam_1(B_73)) | k1_xboole_0=B_73 | k1_tarski(A_27)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_227])).
% 2.07/1.27  tff(c_320, plain, (![A_85, B_86]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_85), B_86))=k3_xboole_0(A_85, k1_setfam_1(B_86)) | k1_xboole_0=B_86)), inference(negUnitSimplification, [status(thm)], [c_164, c_244])).
% 2.07/1.27  tff(c_343, plain, (![A_15, C_63]: (k3_xboole_0(A_15, k1_setfam_1(k1_tarski(C_63)))=k1_setfam_1(k2_tarski(A_15, C_63)) | k1_tarski(C_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_177, c_320])).
% 2.07/1.27  tff(c_354, plain, (![A_15, C_63]: (k1_setfam_1(k2_tarski(A_15, C_63))=k3_xboole_0(A_15, C_63) | k1_tarski(C_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_343])).
% 2.07/1.27  tff(c_355, plain, (![A_15, C_63]: (k1_setfam_1(k2_tarski(A_15, C_63))=k3_xboole_0(A_15, C_63))), inference(negUnitSimplification, [status(thm)], [c_164, c_354])).
% 2.07/1.27  tff(c_48, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.07/1.27  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_48])).
% 2.07/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.27  
% 2.07/1.27  Inference rules
% 2.07/1.27  ----------------------
% 2.07/1.27  #Ref     : 0
% 2.07/1.27  #Sup     : 68
% 2.07/1.27  #Fact    : 0
% 2.07/1.27  #Define  : 0
% 2.07/1.27  #Split   : 0
% 2.07/1.27  #Chain   : 0
% 2.07/1.27  #Close   : 0
% 2.07/1.27  
% 2.07/1.27  Ordering : KBO
% 2.07/1.27  
% 2.07/1.27  Simplification rules
% 2.07/1.27  ----------------------
% 2.07/1.27  #Subsume      : 2
% 2.07/1.27  #Demod        : 24
% 2.07/1.27  #Tautology    : 45
% 2.07/1.27  #SimpNegUnit  : 8
% 2.07/1.27  #BackRed      : 1
% 2.07/1.27  
% 2.07/1.27  #Partial instantiations: 0
% 2.07/1.27  #Strategies tried      : 1
% 2.07/1.27  
% 2.07/1.27  Timing (in seconds)
% 2.07/1.27  ----------------------
% 2.07/1.28  Preprocessing        : 0.30
% 2.07/1.28  Parsing              : 0.15
% 2.07/1.28  CNF conversion       : 0.02
% 2.07/1.28  Main loop            : 0.21
% 2.07/1.28  Inferencing          : 0.08
% 2.07/1.28  Reduction            : 0.07
% 2.07/1.28  Demodulation         : 0.05
% 2.07/1.28  BG Simplification    : 0.02
% 2.07/1.28  Subsumption          : 0.03
% 2.07/1.28  Abstraction          : 0.02
% 2.07/1.28  MUC search           : 0.00
% 2.07/1.28  Cooper               : 0.00
% 2.07/1.28  Total                : 0.53
% 2.07/1.28  Index Insertion      : 0.00
% 2.07/1.28  Index Deletion       : 0.00
% 2.07/1.28  Index Matching       : 0.00
% 2.07/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
