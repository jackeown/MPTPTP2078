%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:04 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :   57 (  74 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  70 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_232,plain,(
    ! [A_88,B_89,C_90] : k5_xboole_0(k5_xboole_0(A_88,B_89),C_90) = k5_xboole_0(A_88,k5_xboole_0(B_89,C_90)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_462,plain,(
    ! [A_98,B_99,C_100] : k5_xboole_0(k5_xboole_0(A_98,B_99),C_100) = k5_xboole_0(B_99,k5_xboole_0(A_98,C_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_232])).

tff(c_4367,plain,(
    ! [A_162,B_163,C_164] : k5_xboole_0(k3_xboole_0(A_162,B_163),k5_xboole_0(A_162,C_164)) = k5_xboole_0(k4_xboole_0(A_162,B_163),C_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_462])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_156,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_165,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_156])).

tff(c_302,plain,(
    ! [C_91,A_92,B_93] : k5_xboole_0(C_91,k5_xboole_0(A_92,B_93)) = k5_xboole_0(A_92,k5_xboole_0(B_93,C_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_4])).

tff(c_396,plain,(
    ! [B_2,A_1,A_92] : k5_xboole_0(k3_xboole_0(B_2,A_1),k5_xboole_0(A_92,A_1)) = k5_xboole_0(A_92,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_302])).

tff(c_4380,plain,(
    ! [A_162,C_164] : k5_xboole_0(k4_xboole_0(A_162,C_164),C_164) = k5_xboole_0(A_162,k4_xboole_0(C_164,A_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_396])).

tff(c_4660,plain,(
    ! [A_165,C_166] : k5_xboole_0(k4_xboole_0(A_165,C_166),C_166) = k2_xboole_0(A_165,C_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4380])).

tff(c_4830,plain,(
    ! [C_167,A_168] : k5_xboole_0(C_167,k4_xboole_0(A_168,C_167)) = k2_xboole_0(A_168,C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_4660,c_4])).

tff(c_4915,plain,(
    ! [C_167,A_168] : k2_xboole_0(C_167,A_168) = k2_xboole_0(A_168,C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_4830,c_18])).

tff(c_42,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_180,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_187,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_180])).

tff(c_221,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_4950,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4915,c_221])).

tff(c_4954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4950])).

tff(c_4955,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_130,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(A_59,C_60)
      | ~ r1_tarski(k2_tarski(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_139,plain,(
    ! [A_59,B_61,B_10] : r2_hidden(A_59,k2_xboole_0(k2_tarski(A_59,B_61),B_10)) ),
    inference(resolution,[status(thm)],[c_14,c_130])).

tff(c_4962,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4955,c_139])).

tff(c_4972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:32:49 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.32/2.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.68  
% 7.32/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.68  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 7.32/2.68  
% 7.32/2.68  %Foreground sorts:
% 7.32/2.68  
% 7.32/2.68  
% 7.32/2.68  %Background operators:
% 7.32/2.68  
% 7.32/2.68  
% 7.32/2.68  %Foreground operators:
% 7.32/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.32/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.32/2.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.32/2.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.32/2.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.32/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.32/2.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.32/2.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.32/2.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.32/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.32/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.32/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.32/2.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.32/2.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.32/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.32/2.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.32/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.32/2.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.32/2.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.32/2.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.32/2.68  
% 7.32/2.69  tff(f_68, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 7.32/2.69  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.32/2.69  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.32/2.69  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.32/2.69  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.32/2.69  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.32/2.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.32/2.69  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.32/2.69  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.32/2.69  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.32/2.69  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.32/2.69  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.32/2.69  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.32/2.69  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.32/2.69  tff(c_232, plain, (![A_88, B_89, C_90]: (k5_xboole_0(k5_xboole_0(A_88, B_89), C_90)=k5_xboole_0(A_88, k5_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.32/2.69  tff(c_462, plain, (![A_98, B_99, C_100]: (k5_xboole_0(k5_xboole_0(A_98, B_99), C_100)=k5_xboole_0(B_99, k5_xboole_0(A_98, C_100)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_232])).
% 7.32/2.69  tff(c_4367, plain, (![A_162, B_163, C_164]: (k5_xboole_0(k3_xboole_0(A_162, B_163), k5_xboole_0(A_162, C_164))=k5_xboole_0(k4_xboole_0(A_162, B_163), C_164))), inference(superposition, [status(thm), theory('equality')], [c_12, c_462])).
% 7.32/2.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.32/2.69  tff(c_156, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.32/2.69  tff(c_165, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_156])).
% 7.32/2.69  tff(c_302, plain, (![C_91, A_92, B_93]: (k5_xboole_0(C_91, k5_xboole_0(A_92, B_93))=k5_xboole_0(A_92, k5_xboole_0(B_93, C_91)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_4])).
% 7.32/2.69  tff(c_396, plain, (![B_2, A_1, A_92]: (k5_xboole_0(k3_xboole_0(B_2, A_1), k5_xboole_0(A_92, A_1))=k5_xboole_0(A_92, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_302])).
% 7.32/2.69  tff(c_4380, plain, (![A_162, C_164]: (k5_xboole_0(k4_xboole_0(A_162, C_164), C_164)=k5_xboole_0(A_162, k4_xboole_0(C_164, A_162)))), inference(superposition, [status(thm), theory('equality')], [c_4367, c_396])).
% 7.32/2.69  tff(c_4660, plain, (![A_165, C_166]: (k5_xboole_0(k4_xboole_0(A_165, C_166), C_166)=k2_xboole_0(A_165, C_166))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4380])).
% 7.32/2.69  tff(c_4830, plain, (![C_167, A_168]: (k5_xboole_0(C_167, k4_xboole_0(A_168, C_167))=k2_xboole_0(A_168, C_167))), inference(superposition, [status(thm), theory('equality')], [c_4660, c_4])).
% 7.32/2.69  tff(c_4915, plain, (![C_167, A_168]: (k2_xboole_0(C_167, A_168)=k2_xboole_0(A_168, C_167))), inference(superposition, [status(thm), theory('equality')], [c_4830, c_18])).
% 7.32/2.69  tff(c_42, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.32/2.69  tff(c_180, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.32/2.69  tff(c_187, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_180])).
% 7.32/2.69  tff(c_221, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_187])).
% 7.32/2.69  tff(c_4950, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4915, c_221])).
% 7.32/2.69  tff(c_4954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_4950])).
% 7.32/2.69  tff(c_4955, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_187])).
% 7.32/2.69  tff(c_130, plain, (![A_59, C_60, B_61]: (r2_hidden(A_59, C_60) | ~r1_tarski(k2_tarski(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.32/2.69  tff(c_139, plain, (![A_59, B_61, B_10]: (r2_hidden(A_59, k2_xboole_0(k2_tarski(A_59, B_61), B_10)))), inference(resolution, [status(thm)], [c_14, c_130])).
% 7.32/2.69  tff(c_4962, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4955, c_139])).
% 7.32/2.69  tff(c_4972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_4962])).
% 7.32/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.69  
% 7.32/2.69  Inference rules
% 7.32/2.69  ----------------------
% 7.32/2.69  #Ref     : 0
% 7.32/2.69  #Sup     : 1267
% 7.32/2.69  #Fact    : 0
% 7.32/2.69  #Define  : 0
% 7.32/2.69  #Split   : 1
% 7.32/2.69  #Chain   : 0
% 7.32/2.69  #Close   : 0
% 7.32/2.69  
% 7.32/2.69  Ordering : KBO
% 7.32/2.69  
% 7.32/2.69  Simplification rules
% 7.32/2.69  ----------------------
% 7.32/2.69  #Subsume      : 165
% 7.32/2.69  #Demod        : 894
% 7.32/2.69  #Tautology    : 207
% 7.32/2.69  #SimpNegUnit  : 1
% 7.32/2.69  #BackRed      : 3
% 7.32/2.69  
% 7.32/2.69  #Partial instantiations: 0
% 7.32/2.69  #Strategies tried      : 1
% 7.32/2.69  
% 7.32/2.69  Timing (in seconds)
% 7.32/2.69  ----------------------
% 7.32/2.70  Preprocessing        : 0.33
% 7.32/2.70  Parsing              : 0.17
% 7.32/2.70  CNF conversion       : 0.02
% 7.32/2.70  Main loop            : 1.60
% 7.32/2.70  Inferencing          : 0.32
% 7.32/2.70  Reduction            : 1.03
% 7.32/2.70  Demodulation         : 0.95
% 7.32/2.70  BG Simplification    : 0.06
% 7.32/2.70  Subsumption          : 0.15
% 7.32/2.70  Abstraction          : 0.08
% 7.32/2.70  MUC search           : 0.00
% 7.32/2.70  Cooper               : 0.00
% 7.32/2.70  Total                : 1.95
% 7.32/2.70  Index Insertion      : 0.00
% 7.32/2.70  Index Deletion       : 0.00
% 7.32/2.70  Index Matching       : 0.00
% 7.32/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
