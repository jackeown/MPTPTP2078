%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:41 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 123 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 ( 141 expanded)
%              Number of equality atoms :   15 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_117,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_18])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_124,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_14])).

tff(c_126,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_46])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(k2_xboole_0(B_8,A_7))
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_10])).

tff(c_153,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_153,c_4])).

tff(c_16,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_168,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_16])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_167,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_12])).

tff(c_258,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_261,plain,(
    ! [A_9,C_53] :
      ( ~ r1_xboole_0(A_9,'#skF_6')
      | ~ r2_hidden(C_53,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_258])).

tff(c_263,plain,(
    ! [C_53] : ~ r2_hidden(C_53,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_261])).

tff(c_26,plain,(
    ! [D_21,B_17] : r2_hidden(D_21,k2_tarski(D_21,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_133,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_26])).

tff(c_161,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_133])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.29  
% 2.01/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.01/1.30  
% 2.01/1.30  %Foreground sorts:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Background operators:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Foreground operators:
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.30  
% 2.01/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.01/1.31  tff(f_81, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.01/1.31  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.01/1.31  tff(f_56, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.01/1.31  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.01/1.31  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.01/1.31  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.01/1.31  tff(f_52, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.01/1.31  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.01/1.31  tff(f_71, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.01/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.01/1.31  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.01/1.31  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.31  tff(c_117, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_18])).
% 2.01/1.31  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.01/1.31  tff(c_124, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_117, c_14])).
% 2.01/1.31  tff(c_126, plain, (k2_xboole_0(k1_xboole_0, '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_46])).
% 2.01/1.31  tff(c_10, plain, (![B_8, A_7]: (~v1_xboole_0(k2_xboole_0(B_8, A_7)) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.01/1.31  tff(c_146, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_126, c_10])).
% 2.01/1.31  tff(c_153, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_146])).
% 2.01/1.31  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.01/1.31  tff(c_159, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_153, c_4])).
% 2.01/1.31  tff(c_16, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.01/1.31  tff(c_168, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_16])).
% 2.01/1.31  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.31  tff(c_167, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_12])).
% 2.01/1.31  tff(c_258, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.31  tff(c_261, plain, (![A_9, C_53]: (~r1_xboole_0(A_9, '#skF_6') | ~r2_hidden(C_53, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_258])).
% 2.01/1.31  tff(c_263, plain, (![C_53]: (~r2_hidden(C_53, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_261])).
% 2.01/1.31  tff(c_26, plain, (![D_21, B_17]: (r2_hidden(D_21, k2_tarski(D_21, B_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.01/1.31  tff(c_133, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_124, c_26])).
% 2.01/1.31  tff(c_161, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_133])).
% 2.01/1.31  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_161])).
% 2.01/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.31  
% 2.01/1.31  Inference rules
% 2.01/1.31  ----------------------
% 2.01/1.31  #Ref     : 0
% 2.01/1.31  #Sup     : 55
% 2.01/1.31  #Fact    : 0
% 2.01/1.31  #Define  : 0
% 2.01/1.31  #Split   : 1
% 2.01/1.31  #Chain   : 0
% 2.01/1.31  #Close   : 0
% 2.01/1.31  
% 2.01/1.31  Ordering : KBO
% 2.01/1.31  
% 2.01/1.31  Simplification rules
% 2.01/1.31  ----------------------
% 2.01/1.31  #Subsume      : 0
% 2.01/1.31  #Demod        : 29
% 2.01/1.31  #Tautology    : 44
% 2.01/1.31  #SimpNegUnit  : 2
% 2.01/1.31  #BackRed      : 14
% 2.01/1.31  
% 2.01/1.31  #Partial instantiations: 0
% 2.01/1.31  #Strategies tried      : 1
% 2.01/1.31  
% 2.01/1.31  Timing (in seconds)
% 2.01/1.31  ----------------------
% 2.01/1.31  Preprocessing        : 0.33
% 2.01/1.31  Parsing              : 0.18
% 2.01/1.31  CNF conversion       : 0.02
% 2.01/1.31  Main loop            : 0.17
% 2.01/1.31  Inferencing          : 0.05
% 2.01/1.31  Reduction            : 0.06
% 2.01/1.31  Demodulation         : 0.05
% 2.01/1.31  BG Simplification    : 0.01
% 2.01/1.31  Subsumption          : 0.03
% 2.01/1.31  Abstraction          : 0.01
% 2.01/1.31  MUC search           : 0.00
% 2.01/1.31  Cooper               : 0.00
% 2.01/1.31  Total                : 0.53
% 2.01/1.31  Index Insertion      : 0.00
% 2.01/1.31  Index Deletion       : 0.00
% 2.01/1.31  Index Matching       : 0.00
% 2.01/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
