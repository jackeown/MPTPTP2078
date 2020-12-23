%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:33 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 103 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 169 expanded)
%              Number of equality atoms :   26 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    k2_xboole_0(k4_xboole_0('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_49,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k4_xboole_0('#skF_6',k1_tarski('#skF_5'))) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_50,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24,c_49])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1348,plain,(
    ! [A_1471,B_1472,C_1473] :
      ( r2_hidden('#skF_1'(A_1471,B_1472,C_1473),B_1472)
      | r2_hidden('#skF_1'(A_1471,B_1472,C_1473),A_1471)
      | r2_hidden('#skF_2'(A_1471,B_1472,C_1473),C_1473)
      | k2_xboole_0(A_1471,B_1472) = C_1473 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2079,plain,(
    ! [A_1801,B_1802] :
      ( r2_hidden('#skF_1'(A_1801,B_1802,A_1801),B_1802)
      | r2_hidden('#skF_2'(A_1801,B_1802,A_1801),A_1801)
      | k2_xboole_0(A_1801,B_1802) = A_1801 ) ),
    inference(resolution,[status(thm)],[c_1348,c_18])).

tff(c_1845,plain,(
    ! [A_1680,B_1681,C_1682] :
      ( r2_hidden('#skF_1'(A_1680,B_1681,C_1682),B_1681)
      | r2_hidden('#skF_1'(A_1680,B_1681,C_1682),A_1680)
      | ~ r2_hidden('#skF_2'(A_1680,B_1681,C_1682),A_1680)
      | k2_xboole_0(A_1680,B_1681) = C_1682 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1921,plain,(
    ! [A_1680,B_1681] :
      ( r2_hidden('#skF_1'(A_1680,B_1681,A_1680),B_1681)
      | ~ r2_hidden('#skF_2'(A_1680,B_1681,A_1680),A_1680)
      | k2_xboole_0(A_1680,B_1681) = A_1680 ) ),
    inference(resolution,[status(thm)],[c_1845,c_14])).

tff(c_2156,plain,(
    ! [A_1831,B_1832] :
      ( r2_hidden('#skF_1'(A_1831,B_1832,A_1831),B_1832)
      | k2_xboole_0(A_1831,B_1832) = A_1831 ) ),
    inference(resolution,[status(thm)],[c_2079,c_1921])).

tff(c_28,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2203,plain,(
    ! [A_1861,A_1862] :
      ( '#skF_1'(A_1861,k1_tarski(A_1862),A_1861) = A_1862
      | k2_xboole_0(A_1861,k1_tarski(A_1862)) = A_1861 ) ),
    inference(resolution,[status(thm)],[c_2156,c_28])).

tff(c_2389,plain,(
    '#skF_1'('#skF_6',k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2203,c_50])).

tff(c_2412,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6'),'#skF_6')
    | k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2389,c_14])).

tff(c_2460,plain,
    ( ~ r2_hidden('#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6'),'#skF_6')
    | k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2412])).

tff(c_2461,plain,(
    ~ r2_hidden('#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2460])).

tff(c_2415,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6'),'#skF_6')
    | k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2389,c_18])).

tff(c_2463,plain,
    ( r2_hidden('#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6'),'#skF_6')
    | k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2415])).

tff(c_2464,plain,(
    r2_hidden('#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2463])).

tff(c_2476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2461,c_2464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:44:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.74  
% 3.97/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.75  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.97/1.75  
% 3.97/1.75  %Foreground sorts:
% 3.97/1.75  
% 3.97/1.75  
% 3.97/1.75  %Background operators:
% 3.97/1.75  
% 3.97/1.75  
% 3.97/1.75  %Foreground operators:
% 3.97/1.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.97/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.97/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.97/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.97/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.97/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.97/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.75  tff('#skF_5', type, '#skF_5': $i).
% 3.97/1.75  tff('#skF_6', type, '#skF_6': $i).
% 3.97/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.97/1.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.97/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.97/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.97/1.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.97/1.75  
% 3.97/1.76  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.97/1.76  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.97/1.76  tff(f_60, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 3.97/1.76  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.97/1.76  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.97/1.76  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.97/1.76  tff(c_24, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.97/1.76  tff(c_46, plain, (k2_xboole_0(k4_xboole_0('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.97/1.76  tff(c_49, plain, (k2_xboole_0(k1_tarski('#skF_5'), k4_xboole_0('#skF_6', k1_tarski('#skF_5')))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 3.97/1.76  tff(c_50, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24, c_49])).
% 3.97/1.76  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.97/1.76  tff(c_1348, plain, (![A_1471, B_1472, C_1473]: (r2_hidden('#skF_1'(A_1471, B_1472, C_1473), B_1472) | r2_hidden('#skF_1'(A_1471, B_1472, C_1473), A_1471) | r2_hidden('#skF_2'(A_1471, B_1472, C_1473), C_1473) | k2_xboole_0(A_1471, B_1472)=C_1473)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.76  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.76  tff(c_2079, plain, (![A_1801, B_1802]: (r2_hidden('#skF_1'(A_1801, B_1802, A_1801), B_1802) | r2_hidden('#skF_2'(A_1801, B_1802, A_1801), A_1801) | k2_xboole_0(A_1801, B_1802)=A_1801)), inference(resolution, [status(thm)], [c_1348, c_18])).
% 3.97/1.76  tff(c_1845, plain, (![A_1680, B_1681, C_1682]: (r2_hidden('#skF_1'(A_1680, B_1681, C_1682), B_1681) | r2_hidden('#skF_1'(A_1680, B_1681, C_1682), A_1680) | ~r2_hidden('#skF_2'(A_1680, B_1681, C_1682), A_1680) | k2_xboole_0(A_1680, B_1681)=C_1682)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.76  tff(c_14, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.97/1.76  tff(c_1921, plain, (![A_1680, B_1681]: (r2_hidden('#skF_1'(A_1680, B_1681, A_1680), B_1681) | ~r2_hidden('#skF_2'(A_1680, B_1681, A_1680), A_1680) | k2_xboole_0(A_1680, B_1681)=A_1680)), inference(resolution, [status(thm)], [c_1845, c_14])).
% 3.97/1.76  tff(c_2156, plain, (![A_1831, B_1832]: (r2_hidden('#skF_1'(A_1831, B_1832, A_1831), B_1832) | k2_xboole_0(A_1831, B_1832)=A_1831)), inference(resolution, [status(thm)], [c_2079, c_1921])).
% 3.97/1.76  tff(c_28, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.97/1.76  tff(c_2203, plain, (![A_1861, A_1862]: ('#skF_1'(A_1861, k1_tarski(A_1862), A_1861)=A_1862 | k2_xboole_0(A_1861, k1_tarski(A_1862))=A_1861)), inference(resolution, [status(thm)], [c_2156, c_28])).
% 3.97/1.76  tff(c_2389, plain, ('#skF_1'('#skF_6', k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2203, c_50])).
% 3.97/1.76  tff(c_2412, plain, (~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6'), '#skF_6') | k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2389, c_14])).
% 3.97/1.76  tff(c_2460, plain, (~r2_hidden('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6'), '#skF_6') | k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2412])).
% 3.97/1.76  tff(c_2461, plain, (~r2_hidden('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_2460])).
% 3.97/1.76  tff(c_2415, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6'), '#skF_6') | k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2389, c_18])).
% 3.97/1.76  tff(c_2463, plain, (r2_hidden('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6'), '#skF_6') | k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2415])).
% 3.97/1.76  tff(c_2464, plain, (r2_hidden('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_2463])).
% 3.97/1.76  tff(c_2476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2461, c_2464])).
% 3.97/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.76  
% 3.97/1.76  Inference rules
% 3.97/1.76  ----------------------
% 3.97/1.76  #Ref     : 0
% 3.97/1.76  #Sup     : 415
% 3.97/1.76  #Fact    : 6
% 3.97/1.76  #Define  : 0
% 3.97/1.76  #Split   : 1
% 3.97/1.76  #Chain   : 0
% 3.97/1.76  #Close   : 0
% 3.97/1.76  
% 3.97/1.76  Ordering : KBO
% 3.97/1.76  
% 3.97/1.76  Simplification rules
% 3.97/1.76  ----------------------
% 3.97/1.76  #Subsume      : 63
% 3.97/1.76  #Demod        : 55
% 3.97/1.76  #Tautology    : 95
% 3.97/1.76  #SimpNegUnit  : 8
% 3.97/1.76  #BackRed      : 2
% 3.97/1.76  
% 3.97/1.76  #Partial instantiations: 882
% 3.97/1.76  #Strategies tried      : 1
% 3.97/1.76  
% 3.97/1.76  Timing (in seconds)
% 3.97/1.76  ----------------------
% 3.97/1.76  Preprocessing        : 0.31
% 3.97/1.76  Parsing              : 0.15
% 3.97/1.76  CNF conversion       : 0.02
% 3.97/1.76  Main loop            : 0.69
% 3.97/1.76  Inferencing          : 0.28
% 3.97/1.76  Reduction            : 0.18
% 3.97/1.76  Demodulation         : 0.13
% 3.97/1.76  BG Simplification    : 0.03
% 3.97/1.76  Subsumption          : 0.16
% 3.97/1.76  Abstraction          : 0.04
% 3.97/1.76  MUC search           : 0.00
% 3.97/1.76  Cooper               : 0.00
% 3.97/1.76  Total                : 1.02
% 3.97/1.76  Index Insertion      : 0.00
% 3.97/1.76  Index Deletion       : 0.00
% 3.97/1.76  Index Matching       : 0.00
% 3.97/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
