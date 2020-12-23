%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:55 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   49 (  76 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 101 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(c_43,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_tarski(A_25)) = k1_ordinal1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    ! [A_25] : r1_tarski(A_25,k1_ordinal1(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_16])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,k1_tarski(B_19)) = A_18
      | r2_hidden(B_19,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_tarski(A_20)) = k1_ordinal1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_230,plain,(
    ! [B_60,A_61] :
      ( k4_xboole_0(k2_xboole_0(B_60,k1_tarski(A_61)),k1_tarski(A_61)) = B_60
      | r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_260,plain,(
    ! [A_62] :
      ( k4_xboole_0(k1_ordinal1(A_62),k1_tarski(A_62)) = A_62
      | r2_hidden(A_62,A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_230])).

tff(c_312,plain,(
    ! [B_72] :
      ( k1_ordinal1(B_72) = B_72
      | r2_hidden(B_72,B_72)
      | r2_hidden(B_72,k1_ordinal1(B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_260])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_2',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_319,plain,
    ( k1_ordinal1('#skF_2') = '#skF_2'
    | r2_hidden('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_312,c_30])).

tff(c_320,plain,(
    r2_hidden('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_324,plain,(
    ! [B_73] :
      ( r2_hidden('#skF_2',B_73)
      | ~ r1_tarski('#skF_2',B_73) ) ),
    inference(resolution,[status(thm)],[c_320,c_4])).

tff(c_329,plain,(
    ~ r1_tarski('#skF_2',k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_324,c_30])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_329])).

tff(c_336,plain,(
    ~ r2_hidden('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_335,plain,(
    k1_ordinal1('#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_177,plain,(
    ! [A_50,C_51,B_52] :
      ( r2_hidden(A_50,C_51)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(A_50,B_52),C_51),C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_193,plain,(
    ! [A_53,C_54] :
      ( r2_hidden(A_53,C_54)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_53),C_54),C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_177])).

tff(c_217,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | ~ r1_tarski(k2_xboole_0(B_58,k1_tarski(A_57)),B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_193])).

tff(c_228,plain,(
    ! [A_20] :
      ( r2_hidden(A_20,A_20)
      | ~ r1_tarski(k1_ordinal1(A_20),A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_217])).

tff(c_350,plain,
    ( r2_hidden('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_228])).

tff(c_365,plain,(
    r2_hidden('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_350])).

tff(c_370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:44:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.18/1.29  
% 2.18/1.29  %Foreground sorts:
% 2.18/1.29  
% 2.18/1.29  
% 2.18/1.29  %Background operators:
% 2.18/1.29  
% 2.18/1.29  
% 2.18/1.29  %Foreground operators:
% 2.18/1.29  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.29  
% 2.18/1.30  tff(f_60, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.18/1.30  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.18/1.30  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.18/1.30  tff(f_49, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 2.18/1.30  tff(f_63, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.18/1.30  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.18/1.30  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.18/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.18/1.30  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.30  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.18/1.30  tff(c_43, plain, (![A_25]: (k2_xboole_0(A_25, k1_tarski(A_25))=k1_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.30  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.18/1.30  tff(c_49, plain, (![A_25]: (r1_tarski(A_25, k1_ordinal1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_16])).
% 2.18/1.30  tff(c_26, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k1_tarski(B_19))=A_18 | r2_hidden(B_19, A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.30  tff(c_28, plain, (![A_20]: (k2_xboole_0(A_20, k1_tarski(A_20))=k1_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.30  tff(c_230, plain, (![B_60, A_61]: (k4_xboole_0(k2_xboole_0(B_60, k1_tarski(A_61)), k1_tarski(A_61))=B_60 | r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.30  tff(c_260, plain, (![A_62]: (k4_xboole_0(k1_ordinal1(A_62), k1_tarski(A_62))=A_62 | r2_hidden(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_28, c_230])).
% 2.18/1.30  tff(c_312, plain, (![B_72]: (k1_ordinal1(B_72)=B_72 | r2_hidden(B_72, B_72) | r2_hidden(B_72, k1_ordinal1(B_72)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_260])).
% 2.18/1.30  tff(c_30, plain, (~r2_hidden('#skF_2', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.30  tff(c_319, plain, (k1_ordinal1('#skF_2')='#skF_2' | r2_hidden('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_312, c_30])).
% 2.18/1.30  tff(c_320, plain, (r2_hidden('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_319])).
% 2.18/1.30  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.30  tff(c_324, plain, (![B_73]: (r2_hidden('#skF_2', B_73) | ~r1_tarski('#skF_2', B_73))), inference(resolution, [status(thm)], [c_320, c_4])).
% 2.18/1.30  tff(c_329, plain, (~r1_tarski('#skF_2', k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_324, c_30])).
% 2.18/1.30  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_329])).
% 2.18/1.30  tff(c_336, plain, (~r2_hidden('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_319])).
% 2.18/1.30  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.30  tff(c_335, plain, (k1_ordinal1('#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_319])).
% 2.18/1.30  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.30  tff(c_18, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.30  tff(c_177, plain, (![A_50, C_51, B_52]: (r2_hidden(A_50, C_51) | ~r1_tarski(k2_xboole_0(k2_tarski(A_50, B_52), C_51), C_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.30  tff(c_193, plain, (![A_53, C_54]: (r2_hidden(A_53, C_54) | ~r1_tarski(k2_xboole_0(k1_tarski(A_53), C_54), C_54))), inference(superposition, [status(thm), theory('equality')], [c_18, c_177])).
% 2.18/1.30  tff(c_217, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | ~r1_tarski(k2_xboole_0(B_58, k1_tarski(A_57)), B_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_193])).
% 2.18/1.30  tff(c_228, plain, (![A_20]: (r2_hidden(A_20, A_20) | ~r1_tarski(k1_ordinal1(A_20), A_20))), inference(superposition, [status(thm), theory('equality')], [c_28, c_217])).
% 2.18/1.30  tff(c_350, plain, (r2_hidden('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_228])).
% 2.18/1.30  tff(c_365, plain, (r2_hidden('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_350])).
% 2.18/1.30  tff(c_370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_365])).
% 2.18/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  Inference rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Ref     : 0
% 2.18/1.30  #Sup     : 82
% 2.18/1.30  #Fact    : 0
% 2.18/1.30  #Define  : 0
% 2.18/1.30  #Split   : 1
% 2.18/1.30  #Chain   : 0
% 2.18/1.30  #Close   : 0
% 2.18/1.30  
% 2.18/1.30  Ordering : KBO
% 2.18/1.30  
% 2.18/1.30  Simplification rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Subsume      : 19
% 2.18/1.30  #Demod        : 20
% 2.18/1.30  #Tautology    : 31
% 2.18/1.30  #SimpNegUnit  : 1
% 2.18/1.30  #BackRed      : 1
% 2.18/1.30  
% 2.18/1.30  #Partial instantiations: 0
% 2.18/1.30  #Strategies tried      : 1
% 2.18/1.30  
% 2.18/1.30  Timing (in seconds)
% 2.18/1.30  ----------------------
% 2.18/1.30  Preprocessing        : 0.30
% 2.18/1.30  Parsing              : 0.15
% 2.18/1.30  CNF conversion       : 0.02
% 2.18/1.30  Main loop            : 0.24
% 2.18/1.30  Inferencing          : 0.09
% 2.18/1.30  Reduction            : 0.08
% 2.18/1.30  Demodulation         : 0.06
% 2.18/1.30  BG Simplification    : 0.01
% 2.18/1.30  Subsumption          : 0.04
% 2.18/1.30  Abstraction          : 0.01
% 2.18/1.30  MUC search           : 0.00
% 2.18/1.30  Cooper               : 0.00
% 2.18/1.30  Total                : 0.57
% 2.18/1.30  Index Insertion      : 0.00
% 2.18/1.30  Index Deletion       : 0.00
% 2.18/1.31  Index Matching       : 0.00
% 2.18/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
