%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:43 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 131 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 148 expanded)
%              Number of equality atoms :   15 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_66,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_54,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_75,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,A_46) = k2_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90,plain,(
    ! [A_46,B_45] : r1_tarski(A_46,k2_xboole_0(B_45,A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_28])).

tff(c_126,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_90])).

tff(c_24,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_126,c_24])).

tff(c_26,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_153,plain,(
    ! [A_19] : r1_xboole_0(A_19,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_26])).

tff(c_459,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_540,plain,(
    ! [A_72,B_73,B_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | r1_tarski(k3_xboole_0(A_72,B_73),B_74) ) ),
    inference(resolution,[status(thm)],[c_459,c_12])).

tff(c_151,plain,(
    ! [A_18] :
      ( A_18 = '#skF_7'
      | ~ r1_tarski(A_18,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_24])).

tff(c_553,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = '#skF_7'
      | ~ r1_xboole_0(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_540,c_151])).

tff(c_558,plain,(
    ! [A_77] : k3_xboole_0(A_77,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_153,c_553])).

tff(c_566,plain,(
    ! [A_77,C_12] :
      ( ~ r1_xboole_0(A_77,'#skF_7')
      | ~ r2_hidden(C_12,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_12])).

tff(c_573,plain,(
    ! [C_12] : ~ r2_hidden(C_12,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_566])).

tff(c_135,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_28])).

tff(c_161,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_135])).

tff(c_172,plain,(
    ! [A_53] :
      ( A_53 = '#skF_7'
      | ~ r1_tarski(A_53,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_24])).

tff(c_184,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_161,c_172])).

tff(c_34,plain,(
    ! [D_27,B_23] : r2_hidden(D_27,k2_tarski(D_27,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_200,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_34])).

tff(c_586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_573,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.33  
% 2.40/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.40/1.33  
% 2.40/1.33  %Foreground sorts:
% 2.40/1.33  
% 2.40/1.33  
% 2.40/1.33  %Background operators:
% 2.40/1.33  
% 2.40/1.33  
% 2.40/1.33  %Foreground operators:
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.40/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.40/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.40/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.40/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.40/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.33  
% 2.40/1.34  tff(f_87, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.40/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.40/1.34  tff(f_68, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.40/1.34  tff(f_64, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.40/1.34  tff(f_66, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.40/1.34  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.40/1.34  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.40/1.34  tff(f_77, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.40/1.34  tff(c_54, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.40/1.34  tff(c_75, plain, (![B_45, A_46]: (k2_xboole_0(B_45, A_46)=k2_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.40/1.34  tff(c_28, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.40/1.34  tff(c_90, plain, (![A_46, B_45]: (r1_tarski(A_46, k2_xboole_0(B_45, A_46)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_28])).
% 2.40/1.34  tff(c_126, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_90])).
% 2.40/1.34  tff(c_24, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.40/1.34  tff(c_148, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_126, c_24])).
% 2.40/1.34  tff(c_26, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.40/1.34  tff(c_153, plain, (![A_19]: (r1_xboole_0(A_19, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_26])).
% 2.40/1.34  tff(c_459, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), A_68) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.40/1.34  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.34  tff(c_540, plain, (![A_72, B_73, B_74]: (~r1_xboole_0(A_72, B_73) | r1_tarski(k3_xboole_0(A_72, B_73), B_74))), inference(resolution, [status(thm)], [c_459, c_12])).
% 2.40/1.34  tff(c_151, plain, (![A_18]: (A_18='#skF_7' | ~r1_tarski(A_18, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_24])).
% 2.40/1.34  tff(c_553, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)='#skF_7' | ~r1_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_540, c_151])).
% 2.40/1.34  tff(c_558, plain, (![A_77]: (k3_xboole_0(A_77, '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_153, c_553])).
% 2.40/1.34  tff(c_566, plain, (![A_77, C_12]: (~r1_xboole_0(A_77, '#skF_7') | ~r2_hidden(C_12, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_558, c_12])).
% 2.40/1.34  tff(c_573, plain, (![C_12]: (~r2_hidden(C_12, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_566])).
% 2.40/1.34  tff(c_135, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_28])).
% 2.40/1.34  tff(c_161, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_135])).
% 2.40/1.34  tff(c_172, plain, (![A_53]: (A_53='#skF_7' | ~r1_tarski(A_53, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_24])).
% 2.40/1.34  tff(c_184, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_161, c_172])).
% 2.40/1.34  tff(c_34, plain, (![D_27, B_23]: (r2_hidden(D_27, k2_tarski(D_27, B_23)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.40/1.34  tff(c_200, plain, (r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_184, c_34])).
% 2.40/1.34  tff(c_586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_573, c_200])).
% 2.40/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.34  
% 2.40/1.34  Inference rules
% 2.40/1.34  ----------------------
% 2.40/1.34  #Ref     : 0
% 2.40/1.34  #Sup     : 128
% 2.40/1.34  #Fact    : 0
% 2.40/1.34  #Define  : 0
% 2.40/1.34  #Split   : 2
% 2.40/1.34  #Chain   : 0
% 2.40/1.34  #Close   : 0
% 2.40/1.34  
% 2.40/1.34  Ordering : KBO
% 2.40/1.34  
% 2.40/1.34  Simplification rules
% 2.40/1.34  ----------------------
% 2.40/1.34  #Subsume      : 1
% 2.40/1.34  #Demod        : 82
% 2.40/1.34  #Tautology    : 101
% 2.40/1.34  #SimpNegUnit  : 2
% 2.40/1.34  #BackRed      : 8
% 2.40/1.34  
% 2.40/1.34  #Partial instantiations: 0
% 2.40/1.34  #Strategies tried      : 1
% 2.40/1.34  
% 2.40/1.34  Timing (in seconds)
% 2.40/1.34  ----------------------
% 2.40/1.34  Preprocessing        : 0.31
% 2.40/1.34  Parsing              : 0.16
% 2.40/1.34  CNF conversion       : 0.02
% 2.40/1.34  Main loop            : 0.25
% 2.40/1.34  Inferencing          : 0.08
% 2.40/1.34  Reduction            : 0.09
% 2.40/1.34  Demodulation         : 0.07
% 2.40/1.34  BG Simplification    : 0.01
% 2.40/1.34  Subsumption          : 0.05
% 2.40/1.34  Abstraction          : 0.02
% 2.40/1.34  MUC search           : 0.00
% 2.40/1.34  Cooper               : 0.00
% 2.40/1.34  Total                : 0.59
% 2.40/1.34  Index Insertion      : 0.00
% 2.40/1.34  Index Deletion       : 0.00
% 2.40/1.34  Index Matching       : 0.00
% 2.40/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
