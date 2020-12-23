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
% DateTime   : Thu Dec  3 09:51:46 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   53 (  93 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 119 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_41,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_67,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_57,plain,(
    ! [B_37,A_38] :
      ( ~ v1_xboole_0(k2_xboole_0(B_37,A_38))
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_57])).

tff(c_62,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_60])).

tff(c_173,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_178,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_173,c_4])).

tff(c_26,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_189,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_178,c_26])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_62,c_189])).

tff(c_24,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_214,plain,(
    ! [A_19] : r1_tarski('#skF_6',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_24])).

tff(c_63,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_105,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_63])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( ~ v1_xboole_0(k2_xboole_0(B_18,A_17))
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_22])).

tff(c_121,plain,(
    v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_199,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_121,c_189])).

tff(c_255,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_199])).

tff(c_40,plain,(
    ! [A_29,C_31,B_30] :
      ( r2_hidden(A_29,C_31)
      | ~ r1_tarski(k2_tarski(A_29,B_30),C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_262,plain,(
    ! [C_31] :
      ( r2_hidden('#skF_4',C_31)
      | ~ r1_tarski('#skF_6',C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_40])).

tff(c_271,plain,(
    ! [C_65] : r2_hidden('#skF_4',C_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_262])).

tff(c_275,plain,(
    ! [C_65] : ~ v1_xboole_0(C_65) ),
    inference(resolution,[status(thm)],[c_271,c_4])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:41:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.22  
% 2.05/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.05/1.22  
% 2.05/1.22  %Foreground sorts:
% 2.05/1.22  
% 2.05/1.22  
% 2.05/1.22  %Background operators:
% 2.05/1.22  
% 2.05/1.22  
% 2.05/1.22  %Foreground operators:
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.05/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.05/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.22  
% 2.14/1.23  tff(f_41, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.14/1.23  tff(f_89, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.14/1.23  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.14/1.23  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.14/1.23  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.14/1.23  tff(f_71, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.14/1.23  tff(f_67, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.14/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.14/1.23  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.14/1.23  tff(c_14, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.23  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.23  tff(c_57, plain, (![B_37, A_38]: (~v1_xboole_0(k2_xboole_0(B_37, A_38)) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.23  tff(c_60, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_42, c_57])).
% 2.14/1.23  tff(c_62, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_60])).
% 2.14/1.23  tff(c_173, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.14/1.23  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.23  tff(c_178, plain, (![A_57, B_58]: (~v1_xboole_0(A_57) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_173, c_4])).
% 2.14/1.23  tff(c_26, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.14/1.23  tff(c_189, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_178, c_26])).
% 2.14/1.23  tff(c_200, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_62, c_189])).
% 2.14/1.23  tff(c_24, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.23  tff(c_214, plain, (![A_19]: (r1_tarski('#skF_6', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_24])).
% 2.14/1.23  tff(c_63, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.23  tff(c_105, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_63])).
% 2.14/1.23  tff(c_22, plain, (![B_18, A_17]: (~v1_xboole_0(k2_xboole_0(B_18, A_17)) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.23  tff(c_117, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_22])).
% 2.14/1.23  tff(c_121, plain, (v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_117])).
% 2.14/1.23  tff(c_199, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_121, c_189])).
% 2.14/1.23  tff(c_255, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_199])).
% 2.14/1.23  tff(c_40, plain, (![A_29, C_31, B_30]: (r2_hidden(A_29, C_31) | ~r1_tarski(k2_tarski(A_29, B_30), C_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.14/1.23  tff(c_262, plain, (![C_31]: (r2_hidden('#skF_4', C_31) | ~r1_tarski('#skF_6', C_31))), inference(superposition, [status(thm), theory('equality')], [c_255, c_40])).
% 2.14/1.23  tff(c_271, plain, (![C_65]: (r2_hidden('#skF_4', C_65))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_262])).
% 2.14/1.23  tff(c_275, plain, (![C_65]: (~v1_xboole_0(C_65))), inference(resolution, [status(thm)], [c_271, c_4])).
% 2.14/1.23  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_62])).
% 2.14/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.23  
% 2.14/1.23  Inference rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Ref     : 0
% 2.14/1.23  #Sup     : 54
% 2.14/1.23  #Fact    : 0
% 2.14/1.23  #Define  : 0
% 2.14/1.23  #Split   : 0
% 2.14/1.23  #Chain   : 0
% 2.14/1.23  #Close   : 0
% 2.14/1.23  
% 2.14/1.23  Ordering : KBO
% 2.14/1.23  
% 2.14/1.23  Simplification rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Subsume      : 8
% 2.14/1.23  #Demod        : 27
% 2.14/1.23  #Tautology    : 34
% 2.14/1.23  #SimpNegUnit  : 4
% 2.14/1.23  #BackRed      : 11
% 2.14/1.23  
% 2.14/1.23  #Partial instantiations: 0
% 2.14/1.23  #Strategies tried      : 1
% 2.14/1.23  
% 2.14/1.23  Timing (in seconds)
% 2.14/1.23  ----------------------
% 2.14/1.24  Preprocessing        : 0.31
% 2.14/1.24  Parsing              : 0.16
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.18
% 2.14/1.24  Inferencing          : 0.06
% 2.14/1.24  Reduction            : 0.06
% 2.14/1.24  Demodulation         : 0.05
% 2.14/1.24  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.03
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.51
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
