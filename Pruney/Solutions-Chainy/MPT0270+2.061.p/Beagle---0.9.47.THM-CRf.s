%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:00 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 156 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 233 expanded)
%              Number of equality atoms :   40 ( 109 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_69,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(k2_xboole_0(A_3,B_4),B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_143,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(k1_tarski(A_44),B_45) = k1_tarski(A_44)
      | r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_69,c_41])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_75,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_160,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_75])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_160])).

tff(c_182,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | k4_xboole_0(k1_tarski(A_15),B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_186,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | k1_tarski('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_22])).

tff(c_189,plain,(
    k1_tarski('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_186])).

tff(c_181,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_332,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_38])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k1_tarski(A_15),B_16) = k1_xboole_0
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_339,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_24])).

tff(c_354,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_339])).

tff(c_264,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(k1_tarski(A_56),B_57) = k1_tarski(A_56)
      | r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_69,c_41])).

tff(c_284,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | k1_tarski(A_56) != k1_xboole_0
      | r2_hidden(A_56,B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_22])).

tff(c_430,plain,(
    ! [A_66,B_67] :
      ( k1_tarski(A_66) != k1_xboole_0
      | r2_hidden(A_66,B_67) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_284])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_454,plain,(
    ! [A_69,A_68] :
      ( A_69 = A_68
      | k1_tarski(A_68) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_430,c_6])).

tff(c_499,plain,(
    '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_454])).

tff(c_500,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_354])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_500])).

tff(c_573,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_574,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_672,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_40])).

tff(c_676,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_24])).

tff(c_686,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_676])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_713,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_8])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( ~ r2_hidden(B_22,A_21)
      | k4_xboole_0(A_21,k1_tarski(B_22)) != A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_751,plain,(
    ! [A_753] :
      ( ~ r2_hidden('#skF_5',A_753)
      | k4_xboole_0(A_753,k1_xboole_0) != A_753 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_30])).

tff(c_766,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_713,c_751])).

tff(c_771,plain,(
    ! [B_756] :
      ( k4_xboole_0(k1_xboole_0,B_756) = k1_xboole_0
      | ~ r2_hidden('#skF_5',B_756) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_24])).

tff(c_777,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_713,c_771])).

tff(c_789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_766,c_777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:57:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.48  
% 2.58/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.49  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.58/1.49  
% 2.58/1.49  %Foreground sorts:
% 2.58/1.49  
% 2.58/1.49  
% 2.58/1.49  %Background operators:
% 2.58/1.49  
% 2.58/1.49  
% 2.58/1.49  %Foreground operators:
% 2.58/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.58/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.58/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.58/1.49  
% 2.58/1.50  tff(f_64, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.58/1.50  tff(f_53, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 2.58/1.50  tff(f_27, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.58/1.50  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 2.58/1.50  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.58/1.50  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.58/1.50  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.58/1.50  tff(c_36, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.50  tff(c_43, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 2.58/1.50  tff(c_69, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.50  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), B_2)=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.50  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.50  tff(c_41, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.58/1.50  tff(c_143, plain, (![A_44, B_45]: (k4_xboole_0(k1_tarski(A_44), B_45)=k1_tarski(A_44) | r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_69, c_41])).
% 2.58/1.50  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.50  tff(c_75, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.58/1.50  tff(c_160, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_143, c_75])).
% 2.58/1.50  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_160])).
% 2.58/1.50  tff(c_182, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.58/1.50  tff(c_22, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | k4_xboole_0(k1_tarski(A_15), B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.58/1.50  tff(c_186, plain, (r2_hidden('#skF_3', '#skF_4') | k1_tarski('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_182, c_22])).
% 2.58/1.50  tff(c_189, plain, (k1_tarski('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_43, c_186])).
% 2.58/1.50  tff(c_181, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 2.58/1.50  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.50  tff(c_332, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_38])).
% 2.58/1.50  tff(c_24, plain, (![A_15, B_16]: (k4_xboole_0(k1_tarski(A_15), B_16)=k1_xboole_0 | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.58/1.50  tff(c_339, plain, (k1_tarski('#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_332, c_24])).
% 2.58/1.50  tff(c_354, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_181, c_339])).
% 2.58/1.50  tff(c_264, plain, (![A_56, B_57]: (k4_xboole_0(k1_tarski(A_56), B_57)=k1_tarski(A_56) | r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_69, c_41])).
% 2.58/1.50  tff(c_284, plain, (![A_56, B_57]: (r2_hidden(A_56, B_57) | k1_tarski(A_56)!=k1_xboole_0 | r2_hidden(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_264, c_22])).
% 2.58/1.50  tff(c_430, plain, (![A_66, B_67]: (k1_tarski(A_66)!=k1_xboole_0 | r2_hidden(A_66, B_67))), inference(factorization, [status(thm), theory('equality')], [c_284])).
% 2.58/1.50  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.50  tff(c_454, plain, (![A_69, A_68]: (A_69=A_68 | k1_tarski(A_68)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_430, c_6])).
% 2.58/1.50  tff(c_499, plain, ('#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_354, c_454])).
% 2.58/1.50  tff(c_500, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_499, c_354])).
% 2.58/1.50  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_500])).
% 2.58/1.50  tff(c_573, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 2.58/1.50  tff(c_574, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 2.58/1.50  tff(c_40, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.50  tff(c_672, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_574, c_40])).
% 2.58/1.50  tff(c_676, plain, (k1_tarski('#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_672, c_24])).
% 2.58/1.50  tff(c_686, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_573, c_676])).
% 2.58/1.50  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.50  tff(c_713, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_686, c_8])).
% 2.58/1.50  tff(c_30, plain, (![B_22, A_21]: (~r2_hidden(B_22, A_21) | k4_xboole_0(A_21, k1_tarski(B_22))!=A_21)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.58/1.50  tff(c_751, plain, (![A_753]: (~r2_hidden('#skF_5', A_753) | k4_xboole_0(A_753, k1_xboole_0)!=A_753)), inference(superposition, [status(thm), theory('equality')], [c_686, c_30])).
% 2.58/1.50  tff(c_766, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_713, c_751])).
% 2.58/1.50  tff(c_771, plain, (![B_756]: (k4_xboole_0(k1_xboole_0, B_756)=k1_xboole_0 | ~r2_hidden('#skF_5', B_756))), inference(superposition, [status(thm), theory('equality')], [c_686, c_24])).
% 2.58/1.50  tff(c_777, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_713, c_771])).
% 2.58/1.50  tff(c_789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_766, c_777])).
% 2.58/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.50  
% 2.58/1.50  Inference rules
% 2.58/1.50  ----------------------
% 2.58/1.50  #Ref     : 0
% 2.58/1.50  #Sup     : 189
% 2.58/1.50  #Fact    : 2
% 2.58/1.50  #Define  : 0
% 2.58/1.50  #Split   : 2
% 2.58/1.50  #Chain   : 0
% 2.58/1.50  #Close   : 0
% 2.58/1.50  
% 2.58/1.50  Ordering : KBO
% 2.58/1.50  
% 2.58/1.50  Simplification rules
% 2.58/1.50  ----------------------
% 2.58/1.50  #Subsume      : 10
% 2.58/1.50  #Demod        : 26
% 2.58/1.50  #Tautology    : 73
% 2.58/1.50  #SimpNegUnit  : 8
% 2.58/1.50  #BackRed      : 2
% 2.58/1.50  
% 2.58/1.50  #Partial instantiations: 81
% 2.58/1.50  #Strategies tried      : 1
% 2.58/1.50  
% 2.58/1.50  Timing (in seconds)
% 2.58/1.50  ----------------------
% 2.58/1.50  Preprocessing        : 0.34
% 2.58/1.50  Parsing              : 0.17
% 2.58/1.50  CNF conversion       : 0.02
% 2.58/1.50  Main loop            : 0.30
% 2.58/1.50  Inferencing          : 0.13
% 2.58/1.50  Reduction            : 0.08
% 2.58/1.50  Demodulation         : 0.06
% 2.58/1.50  BG Simplification    : 0.02
% 2.58/1.50  Subsumption          : 0.05
% 2.58/1.50  Abstraction          : 0.02
% 2.58/1.50  MUC search           : 0.00
% 2.58/1.50  Cooper               : 0.00
% 2.58/1.50  Total                : 0.67
% 2.58/1.51  Index Insertion      : 0.00
% 2.58/1.51  Index Deletion       : 0.00
% 2.58/1.51  Index Matching       : 0.00
% 2.58/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
