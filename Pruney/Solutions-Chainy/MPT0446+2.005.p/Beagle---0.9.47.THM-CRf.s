%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:26 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   48 (  66 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 107 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_18,plain,
    ( ~ r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_81,plain,(
    ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_93,plain,(
    ! [A_29] :
      ( k2_xboole_0(k1_relat_1(A_29),k2_relat_1(A_29)) = k3_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_102,plain,(
    ! [A_29] :
      ( r1_tarski(k1_relat_1(A_29),k3_relat_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_10])).

tff(c_20,plain,(
    r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_189,plain,(
    ! [A_39,C_40,B_41] :
      ( r2_hidden(A_39,k1_relat_1(C_40))
      | ~ r2_hidden(k4_tarski(A_39,B_41),C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_195,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_189])).

tff(c_199,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_195])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_203,plain,(
    ! [B_42] :
      ( r2_hidden('#skF_2',B_42)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_42) ) ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_207,plain,
    ( r2_hidden('#skF_2',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_203])).

tff(c_222,plain,(
    r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_207])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_222])).

tff(c_225,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_227,plain,(
    ! [A_43] :
      ( k2_xboole_0(k1_relat_1(A_43),k2_relat_1(A_43)) = k3_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [B_16,A_17] : k2_xboole_0(B_16,A_17) = k2_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_17,B_16] : r1_tarski(A_17,k2_xboole_0(B_16,A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_233,plain,(
    ! [A_43] :
      ( r1_tarski(k2_relat_1(A_43),k3_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_39])).

tff(c_373,plain,(
    ! [B_59,C_60,A_61] :
      ( r2_hidden(B_59,k2_relat_1(C_60))
      | ~ r2_hidden(k4_tarski(A_61,B_59),C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_379,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_373])).

tff(c_383,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_379])).

tff(c_393,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_3',B_63)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_63) ) ),
    inference(resolution,[status(thm)],[c_383,c_4])).

tff(c_397,plain,
    ( r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_233,c_393])).

tff(c_412,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_397])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.04/1.28  
% 2.04/1.28  %Foreground sorts:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Background operators:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Foreground operators:
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.04/1.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.04/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.28  
% 2.04/1.29  tff(f_57, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 2.04/1.29  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.04/1.29  tff(f_36, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.04/1.29  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 2.04/1.29  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.04/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.04/1.29  tff(c_18, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.04/1.29  tff(c_81, plain, (~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_18])).
% 2.04/1.29  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.04/1.29  tff(c_93, plain, (![A_29]: (k2_xboole_0(k1_relat_1(A_29), k2_relat_1(A_29))=k3_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.29  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.04/1.29  tff(c_102, plain, (![A_29]: (r1_tarski(k1_relat_1(A_29), k3_relat_1(A_29)) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_93, c_10])).
% 2.04/1.29  tff(c_20, plain, (r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.04/1.29  tff(c_189, plain, (![A_39, C_40, B_41]: (r2_hidden(A_39, k1_relat_1(C_40)) | ~r2_hidden(k4_tarski(A_39, B_41), C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.29  tff(c_195, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_189])).
% 2.04/1.29  tff(c_199, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_195])).
% 2.04/1.29  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.29  tff(c_203, plain, (![B_42]: (r2_hidden('#skF_2', B_42) | ~r1_tarski(k1_relat_1('#skF_4'), B_42))), inference(resolution, [status(thm)], [c_199, c_4])).
% 2.04/1.29  tff(c_207, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_203])).
% 2.04/1.29  tff(c_222, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_207])).
% 2.04/1.29  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_222])).
% 2.04/1.29  tff(c_225, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_18])).
% 2.04/1.29  tff(c_227, plain, (![A_43]: (k2_xboole_0(k1_relat_1(A_43), k2_relat_1(A_43))=k3_relat_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.29  tff(c_24, plain, (![B_16, A_17]: (k2_xboole_0(B_16, A_17)=k2_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.29  tff(c_39, plain, (![A_17, B_16]: (r1_tarski(A_17, k2_xboole_0(B_16, A_17)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_10])).
% 2.04/1.29  tff(c_233, plain, (![A_43]: (r1_tarski(k2_relat_1(A_43), k3_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_227, c_39])).
% 2.04/1.29  tff(c_373, plain, (![B_59, C_60, A_61]: (r2_hidden(B_59, k2_relat_1(C_60)) | ~r2_hidden(k4_tarski(A_61, B_59), C_60) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.29  tff(c_379, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_373])).
% 2.04/1.29  tff(c_383, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_379])).
% 2.04/1.29  tff(c_393, plain, (![B_63]: (r2_hidden('#skF_3', B_63) | ~r1_tarski(k2_relat_1('#skF_4'), B_63))), inference(resolution, [status(thm)], [c_383, c_4])).
% 2.04/1.29  tff(c_397, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_233, c_393])).
% 2.04/1.29  tff(c_412, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_397])).
% 2.04/1.29  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_225, c_412])).
% 2.04/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  Inference rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Ref     : 0
% 2.04/1.29  #Sup     : 82
% 2.04/1.29  #Fact    : 0
% 2.04/1.29  #Define  : 0
% 2.04/1.29  #Split   : 1
% 2.04/1.29  #Chain   : 0
% 2.04/1.29  #Close   : 0
% 2.04/1.29  
% 2.04/1.29  Ordering : KBO
% 2.04/1.29  
% 2.04/1.29  Simplification rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Subsume      : 0
% 2.04/1.29  #Demod        : 31
% 2.04/1.29  #Tautology    : 33
% 2.04/1.29  #SimpNegUnit  : 2
% 2.04/1.29  #BackRed      : 0
% 2.04/1.29  
% 2.04/1.29  #Partial instantiations: 0
% 2.04/1.29  #Strategies tried      : 1
% 2.04/1.29  
% 2.04/1.29  Timing (in seconds)
% 2.04/1.29  ----------------------
% 2.04/1.30  Preprocessing        : 0.26
% 2.04/1.30  Parsing              : 0.14
% 2.04/1.30  CNF conversion       : 0.02
% 2.04/1.30  Main loop            : 0.25
% 2.04/1.30  Inferencing          : 0.09
% 2.04/1.30  Reduction            : 0.08
% 2.04/1.30  Demodulation         : 0.06
% 2.04/1.30  BG Simplification    : 0.01
% 2.04/1.30  Subsumption          : 0.04
% 2.04/1.30  Abstraction          : 0.01
% 2.04/1.30  MUC search           : 0.00
% 2.04/1.30  Cooper               : 0.00
% 2.04/1.30  Total                : 0.53
% 2.04/1.30  Index Insertion      : 0.00
% 2.04/1.30  Index Deletion       : 0.00
% 2.04/1.30  Index Matching       : 0.00
% 2.04/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
