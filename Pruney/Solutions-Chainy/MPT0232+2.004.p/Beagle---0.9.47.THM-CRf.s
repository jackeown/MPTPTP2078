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
% DateTime   : Thu Dec  3 09:49:20 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   55 (  96 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 ( 120 expanded)
%              Number of equality atoms :   25 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_78,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_149,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    ! [A_43] : k1_enumset1(A_43,A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_165,plain,(
    ! [B_65] : k2_tarski(B_65,B_65) = k1_tarski(B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_74])).

tff(c_36,plain,(
    ! [E_19,B_14,C_15] : r2_hidden(E_19,k1_enumset1(E_19,B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_158,plain,(
    ! [A_64,B_65] : r2_hidden(A_64,k2_tarski(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_36])).

tff(c_28,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_81,plain,(
    r1_tarski(k2_tarski('#skF_8','#skF_7'),k1_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_80])).

tff(c_208,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = A_71
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_215,plain,(
    k3_xboole_0(k2_tarski('#skF_8','#skF_7'),k1_tarski('#skF_9')) = k2_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_81,c_208])).

tff(c_245,plain,(
    ! [D_76,B_77,A_78] :
      ( r2_hidden(D_76,B_77)
      | ~ r2_hidden(D_76,k3_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_268,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_85,k2_tarski('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_245])).

tff(c_277,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_158,c_268])).

tff(c_54,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_282,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_277,c_54])).

tff(c_32,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_155,plain,(
    ! [B_65,A_64] : r2_hidden(B_65,k2_tarski(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_32])).

tff(c_278,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_155,c_268])).

tff(c_294,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_278])).

tff(c_298,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_294,c_54])).

tff(c_78,plain,(
    k2_tarski('#skF_7','#skF_8') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    k2_tarski('#skF_8','#skF_7') != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_78])).

tff(c_288,plain,(
    k2_tarski('#skF_8','#skF_7') != k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_82])).

tff(c_300,plain,(
    k2_tarski('#skF_8','#skF_8') != k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_288])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.76  
% 2.71/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.76  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 2.71/1.76  
% 2.71/1.76  %Foreground sorts:
% 2.71/1.76  
% 2.71/1.76  
% 2.71/1.76  %Background operators:
% 2.71/1.76  
% 2.71/1.76  
% 2.71/1.76  %Foreground operators:
% 2.71/1.76  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.71/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.76  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.71/1.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.76  tff('#skF_9', type, '#skF_9': $i).
% 2.71/1.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.71/1.76  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.76  tff('#skF_8', type, '#skF_8': $i).
% 2.71/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.71/1.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.76  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.71/1.76  
% 2.71/1.78  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.71/1.78  tff(f_78, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 2.71/1.78  tff(f_61, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.71/1.78  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.71/1.78  tff(f_85, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.71/1.78  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.71/1.78  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.71/1.78  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.71/1.78  tff(c_149, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.78  tff(c_74, plain, (![A_43]: (k1_enumset1(A_43, A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.78  tff(c_165, plain, (![B_65]: (k2_tarski(B_65, B_65)=k1_tarski(B_65))), inference(superposition, [status(thm), theory('equality')], [c_149, c_74])).
% 2.71/1.78  tff(c_36, plain, (![E_19, B_14, C_15]: (r2_hidden(E_19, k1_enumset1(E_19, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.78  tff(c_158, plain, (![A_64, B_65]: (r2_hidden(A_64, k2_tarski(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_36])).
% 2.71/1.78  tff(c_28, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.78  tff(c_80, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.71/1.78  tff(c_81, plain, (r1_tarski(k2_tarski('#skF_8', '#skF_7'), k1_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_80])).
% 2.71/1.78  tff(c_208, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=A_71 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.78  tff(c_215, plain, (k3_xboole_0(k2_tarski('#skF_8', '#skF_7'), k1_tarski('#skF_9'))=k2_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_81, c_208])).
% 2.71/1.78  tff(c_245, plain, (![D_76, B_77, A_78]: (r2_hidden(D_76, B_77) | ~r2_hidden(D_76, k3_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.71/1.78  tff(c_268, plain, (![D_85]: (r2_hidden(D_85, k1_tarski('#skF_9')) | ~r2_hidden(D_85, k2_tarski('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_215, c_245])).
% 2.71/1.78  tff(c_277, plain, (r2_hidden('#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_158, c_268])).
% 2.71/1.78  tff(c_54, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.71/1.78  tff(c_282, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_277, c_54])).
% 2.71/1.78  tff(c_32, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.78  tff(c_155, plain, (![B_65, A_64]: (r2_hidden(B_65, k2_tarski(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_32])).
% 2.71/1.78  tff(c_278, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_155, c_268])).
% 2.71/1.78  tff(c_294, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_278])).
% 2.71/1.78  tff(c_298, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_294, c_54])).
% 2.71/1.78  tff(c_78, plain, (k2_tarski('#skF_7', '#skF_8')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.71/1.78  tff(c_82, plain, (k2_tarski('#skF_8', '#skF_7')!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_78])).
% 2.71/1.78  tff(c_288, plain, (k2_tarski('#skF_8', '#skF_7')!=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_82])).
% 2.71/1.78  tff(c_300, plain, (k2_tarski('#skF_8', '#skF_8')!=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_288])).
% 2.71/1.78  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_300])).
% 2.71/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.78  
% 2.71/1.78  Inference rules
% 2.71/1.78  ----------------------
% 2.71/1.78  #Ref     : 0
% 2.71/1.78  #Sup     : 49
% 2.71/1.78  #Fact    : 0
% 2.71/1.78  #Define  : 0
% 2.71/1.78  #Split   : 0
% 2.71/1.78  #Chain   : 0
% 2.71/1.78  #Close   : 0
% 2.71/1.78  
% 2.71/1.78  Ordering : KBO
% 2.71/1.78  
% 2.71/1.78  Simplification rules
% 2.71/1.78  ----------------------
% 2.71/1.78  #Subsume      : 0
% 2.71/1.78  #Demod        : 27
% 2.71/1.78  #Tautology    : 41
% 2.71/1.78  #SimpNegUnit  : 1
% 2.71/1.78  #BackRed      : 8
% 2.71/1.78  
% 2.71/1.78  #Partial instantiations: 0
% 2.71/1.78  #Strategies tried      : 1
% 2.71/1.78  
% 2.71/1.78  Timing (in seconds)
% 2.71/1.78  ----------------------
% 2.71/1.79  Preprocessing        : 0.53
% 2.71/1.79  Parsing              : 0.25
% 2.71/1.79  CNF conversion       : 0.04
% 2.71/1.79  Main loop            : 0.33
% 2.71/1.79  Inferencing          : 0.09
% 2.71/1.79  Reduction            : 0.13
% 2.71/1.79  Demodulation         : 0.10
% 2.71/1.79  BG Simplification    : 0.04
% 2.71/1.79  Subsumption          : 0.07
% 2.71/1.79  Abstraction          : 0.02
% 2.71/1.79  MUC search           : 0.00
% 2.71/1.79  Cooper               : 0.00
% 2.71/1.79  Total                : 0.91
% 2.71/1.79  Index Insertion      : 0.00
% 2.71/1.79  Index Deletion       : 0.00
% 2.71/1.79  Index Matching       : 0.00
% 2.71/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
