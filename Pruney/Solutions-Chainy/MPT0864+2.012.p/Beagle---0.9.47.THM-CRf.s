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
% DateTime   : Thu Dec  3 10:09:10 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 100 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    ! [A_30,B_31] : k1_mcart_1(k4_tarski(A_30,B_31)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_43])).

tff(c_68,plain,(
    ! [A_33,B_34] : k2_mcart_1(k4_tarski(A_33,B_34)) = B_34 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_77,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_34,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_85,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_77,c_34])).

tff(c_86,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_88,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_36])).

tff(c_109,plain,(
    ! [A_37,B_38] : k2_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),B_22) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    ! [A_21] : k1_tarski(A_21) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_26])).

tff(c_233,plain,(
    ! [A_59,B_60] : k2_zfmisc_1(k1_tarski(A_59),k1_tarski(B_60)) = k1_tarski(k4_tarski(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( ~ r1_tarski(A_17,k2_zfmisc_1(A_17,B_18))
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_239,plain,(
    ! [A_59,B_60] :
      ( ~ r1_tarski(k1_tarski(A_59),k1_tarski(k4_tarski(A_59,B_60)))
      | k1_tarski(A_59) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_22])).

tff(c_250,plain,(
    ! [A_61,B_62] : ~ r1_tarski(k1_tarski(A_61),k1_tarski(k4_tarski(A_61,B_62))) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_239])).

tff(c_253,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_250])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_253])).

tff(c_257,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_260,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_36])).

tff(c_281,plain,(
    ! [A_63,B_64] : k2_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = A_63 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_288,plain,(
    ! [A_21] : k1_tarski(A_21) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_26])).

tff(c_405,plain,(
    ! [A_85,B_86] : k2_zfmisc_1(k1_tarski(A_85),k1_tarski(B_86)) = k1_tarski(k4_tarski(A_85,B_86)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( ~ r1_tarski(A_17,k2_zfmisc_1(B_18,A_17))
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_414,plain,(
    ! [B_86,A_85] :
      ( ~ r1_tarski(k1_tarski(B_86),k1_tarski(k4_tarski(A_85,B_86)))
      | k1_tarski(B_86) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_20])).

tff(c_426,plain,(
    ! [B_89,A_90] : ~ r1_tarski(k1_tarski(B_89),k1_tarski(k4_tarski(A_90,B_89))) ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_414])).

tff(c_429,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_426])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:21:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.23  
% 2.07/1.23  %Foreground sorts:
% 2.07/1.23  
% 2.07/1.23  
% 2.07/1.23  %Background operators:
% 2.07/1.23  
% 2.07/1.23  
% 2.07/1.23  %Foreground operators:
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.07/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.07/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.07/1.23  
% 2.16/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.24  tff(f_70, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.16/1.24  tff(f_60, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.16/1.24  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.16/1.24  tff(f_54, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.16/1.24  tff(f_51, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.16/1.24  tff(f_49, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.16/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.24  tff(c_36, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.24  tff(c_43, plain, (![A_30, B_31]: (k1_mcart_1(k4_tarski(A_30, B_31))=A_30)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.24  tff(c_52, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_36, c_43])).
% 2.16/1.24  tff(c_68, plain, (![A_33, B_34]: (k2_mcart_1(k4_tarski(A_33, B_34))=B_34)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.24  tff(c_77, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_36, c_68])).
% 2.16/1.24  tff(c_34, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.24  tff(c_85, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_77, c_34])).
% 2.16/1.24  tff(c_86, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_85])).
% 2.16/1.24  tff(c_88, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_36])).
% 2.16/1.24  tff(c_109, plain, (![A_37, B_38]: (k2_xboole_0(A_37, k3_xboole_0(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.24  tff(c_26, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.24  tff(c_116, plain, (![A_21]: (k1_tarski(A_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_26])).
% 2.16/1.24  tff(c_233, plain, (![A_59, B_60]: (k2_zfmisc_1(k1_tarski(A_59), k1_tarski(B_60))=k1_tarski(k4_tarski(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.24  tff(c_22, plain, (![A_17, B_18]: (~r1_tarski(A_17, k2_zfmisc_1(A_17, B_18)) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.24  tff(c_239, plain, (![A_59, B_60]: (~r1_tarski(k1_tarski(A_59), k1_tarski(k4_tarski(A_59, B_60))) | k1_tarski(A_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_233, c_22])).
% 2.16/1.24  tff(c_250, plain, (![A_61, B_62]: (~r1_tarski(k1_tarski(A_61), k1_tarski(k4_tarski(A_61, B_62))))), inference(negUnitSimplification, [status(thm)], [c_116, c_239])).
% 2.16/1.24  tff(c_253, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_250])).
% 2.16/1.24  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_253])).
% 2.16/1.24  tff(c_257, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_85])).
% 2.16/1.24  tff(c_260, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_257, c_36])).
% 2.16/1.24  tff(c_281, plain, (![A_63, B_64]: (k2_xboole_0(A_63, k3_xboole_0(A_63, B_64))=A_63)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.24  tff(c_288, plain, (![A_21]: (k1_tarski(A_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_281, c_26])).
% 2.16/1.24  tff(c_405, plain, (![A_85, B_86]: (k2_zfmisc_1(k1_tarski(A_85), k1_tarski(B_86))=k1_tarski(k4_tarski(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.24  tff(c_20, plain, (![A_17, B_18]: (~r1_tarski(A_17, k2_zfmisc_1(B_18, A_17)) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.24  tff(c_414, plain, (![B_86, A_85]: (~r1_tarski(k1_tarski(B_86), k1_tarski(k4_tarski(A_85, B_86))) | k1_tarski(B_86)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_405, c_20])).
% 2.16/1.24  tff(c_426, plain, (![B_89, A_90]: (~r1_tarski(k1_tarski(B_89), k1_tarski(k4_tarski(A_90, B_89))))), inference(negUnitSimplification, [status(thm)], [c_288, c_414])).
% 2.16/1.24  tff(c_429, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_426])).
% 2.16/1.24  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_429])).
% 2.16/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  Inference rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Ref     : 0
% 2.16/1.24  #Sup     : 97
% 2.16/1.24  #Fact    : 0
% 2.16/1.24  #Define  : 0
% 2.16/1.24  #Split   : 1
% 2.16/1.24  #Chain   : 0
% 2.16/1.24  #Close   : 0
% 2.16/1.24  
% 2.16/1.24  Ordering : KBO
% 2.16/1.24  
% 2.16/1.24  Simplification rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Subsume      : 2
% 2.16/1.24  #Demod        : 17
% 2.16/1.24  #Tautology    : 77
% 2.16/1.24  #SimpNegUnit  : 4
% 2.16/1.24  #BackRed      : 4
% 2.16/1.24  
% 2.16/1.24  #Partial instantiations: 0
% 2.16/1.24  #Strategies tried      : 1
% 2.16/1.24  
% 2.16/1.24  Timing (in seconds)
% 2.16/1.24  ----------------------
% 2.16/1.25  Preprocessing        : 0.30
% 2.16/1.25  Parsing              : 0.16
% 2.16/1.25  CNF conversion       : 0.02
% 2.16/1.25  Main loop            : 0.19
% 2.16/1.25  Inferencing          : 0.08
% 2.16/1.25  Reduction            : 0.06
% 2.16/1.25  Demodulation         : 0.04
% 2.16/1.25  BG Simplification    : 0.01
% 2.16/1.25  Subsumption          : 0.02
% 2.16/1.25  Abstraction          : 0.01
% 2.16/1.25  MUC search           : 0.00
% 2.16/1.25  Cooper               : 0.00
% 2.16/1.25  Total                : 0.52
% 2.16/1.25  Index Insertion      : 0.00
% 2.16/1.25  Index Deletion       : 0.00
% 2.16/1.25  Index Matching       : 0.00
% 2.16/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
