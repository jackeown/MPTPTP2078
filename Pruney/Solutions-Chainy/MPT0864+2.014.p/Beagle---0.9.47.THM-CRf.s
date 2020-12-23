%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:10 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   59 (  95 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 ( 114 expanded)
%              Number of equality atoms :   39 (  94 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

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

tff(c_52,plain,(
    ! [A_29,B_30] : k1_mcart_1(k4_tarski(A_29,B_30)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_52])).

tff(c_77,plain,(
    ! [A_32,B_33] : k2_mcart_1(k4_tarski(A_32,B_33)) = B_33 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_77])).

tff(c_34,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_98,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_86,c_34])).

tff(c_99,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_101,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_36])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [A_34,B_35] : k2_xboole_0(k1_tarski(A_34),B_35) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    ! [A_34] : k1_tarski(A_34) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_93])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_193,plain,(
    ! [A_56,B_57,C_58] : k2_zfmisc_1(k1_tarski(A_56),k2_tarski(B_57,C_58)) = k2_tarski(k4_tarski(A_56,B_57),k4_tarski(A_56,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_215,plain,(
    ! [A_56,C_58] : k2_zfmisc_1(k1_tarski(A_56),k2_tarski(C_58,C_58)) = k1_tarski(k4_tarski(A_56,C_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_10])).

tff(c_240,plain,(
    ! [A_59,C_60] : k2_zfmisc_1(k1_tarski(A_59),k1_tarski(C_60)) = k1_tarski(k4_tarski(A_59,C_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_215])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( ~ r1_tarski(A_16,k2_zfmisc_1(A_16,B_17))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_249,plain,(
    ! [A_59,C_60] :
      ( ~ r1_tarski(k1_tarski(A_59),k1_tarski(k4_tarski(A_59,C_60)))
      | k1_tarski(A_59) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_22])).

tff(c_324,plain,(
    ! [A_66,C_67] : ~ r1_tarski(k1_tarski(A_66),k1_tarski(k4_tarski(A_66,C_67))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_249])).

tff(c_327,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_324])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_327])).

tff(c_331,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_334,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_36])).

tff(c_426,plain,(
    ! [A_88,B_89,C_90] : k2_zfmisc_1(k1_tarski(A_88),k2_tarski(B_89,C_90)) = k2_tarski(k4_tarski(A_88,B_89),k4_tarski(A_88,C_90)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_448,plain,(
    ! [A_88,C_90] : k2_zfmisc_1(k1_tarski(A_88),k2_tarski(C_90,C_90)) = k1_tarski(k4_tarski(A_88,C_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_10])).

tff(c_473,plain,(
    ! [A_91,C_92] : k2_zfmisc_1(k1_tarski(A_91),k1_tarski(C_92)) = k1_tarski(k4_tarski(A_91,C_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_448])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( ~ r1_tarski(A_16,k2_zfmisc_1(B_17,A_16))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_479,plain,(
    ! [C_92,A_91] :
      ( ~ r1_tarski(k1_tarski(C_92),k1_tarski(k4_tarski(A_91,C_92)))
      | k1_tarski(C_92) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_20])).

tff(c_553,plain,(
    ! [C_96,A_97] : ~ r1_tarski(k1_tarski(C_96),k1_tarski(k4_tarski(A_97,C_96))) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_479])).

tff(c_556,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_553])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.29  
% 2.26/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.30  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.26/1.30  
% 2.26/1.30  %Foreground sorts:
% 2.26/1.30  
% 2.26/1.30  
% 2.26/1.30  %Background operators:
% 2.26/1.30  
% 2.26/1.30  
% 2.26/1.30  %Foreground operators:
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.26/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.26/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.26/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.30  
% 2.26/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.26/1.31  tff(f_70, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.26/1.31  tff(f_60, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.26/1.31  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.26/1.31  tff(f_56, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.26/1.31  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.31  tff(f_53, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.26/1.31  tff(f_49, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.26/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.31  tff(c_36, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.31  tff(c_52, plain, (![A_29, B_30]: (k1_mcart_1(k4_tarski(A_29, B_30))=A_29)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.26/1.31  tff(c_61, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_36, c_52])).
% 2.26/1.31  tff(c_77, plain, (![A_32, B_33]: (k2_mcart_1(k4_tarski(A_32, B_33))=B_33)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.26/1.31  tff(c_86, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_36, c_77])).
% 2.26/1.31  tff(c_34, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.31  tff(c_98, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_86, c_34])).
% 2.26/1.31  tff(c_99, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_98])).
% 2.26/1.31  tff(c_101, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_36])).
% 2.26/1.31  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.31  tff(c_93, plain, (![A_34, B_35]: (k2_xboole_0(k1_tarski(A_34), B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.31  tff(c_97, plain, (![A_34]: (k1_tarski(A_34)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_93])).
% 2.26/1.31  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.31  tff(c_193, plain, (![A_56, B_57, C_58]: (k2_zfmisc_1(k1_tarski(A_56), k2_tarski(B_57, C_58))=k2_tarski(k4_tarski(A_56, B_57), k4_tarski(A_56, C_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.31  tff(c_215, plain, (![A_56, C_58]: (k2_zfmisc_1(k1_tarski(A_56), k2_tarski(C_58, C_58))=k1_tarski(k4_tarski(A_56, C_58)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_10])).
% 2.26/1.31  tff(c_240, plain, (![A_59, C_60]: (k2_zfmisc_1(k1_tarski(A_59), k1_tarski(C_60))=k1_tarski(k4_tarski(A_59, C_60)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_215])).
% 2.26/1.31  tff(c_22, plain, (![A_16, B_17]: (~r1_tarski(A_16, k2_zfmisc_1(A_16, B_17)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.31  tff(c_249, plain, (![A_59, C_60]: (~r1_tarski(k1_tarski(A_59), k1_tarski(k4_tarski(A_59, C_60))) | k1_tarski(A_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_240, c_22])).
% 2.26/1.31  tff(c_324, plain, (![A_66, C_67]: (~r1_tarski(k1_tarski(A_66), k1_tarski(k4_tarski(A_66, C_67))))), inference(negUnitSimplification, [status(thm)], [c_97, c_249])).
% 2.26/1.31  tff(c_327, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_324])).
% 2.26/1.31  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_327])).
% 2.26/1.31  tff(c_331, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_98])).
% 2.26/1.31  tff(c_334, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_331, c_36])).
% 2.26/1.31  tff(c_426, plain, (![A_88, B_89, C_90]: (k2_zfmisc_1(k1_tarski(A_88), k2_tarski(B_89, C_90))=k2_tarski(k4_tarski(A_88, B_89), k4_tarski(A_88, C_90)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.31  tff(c_448, plain, (![A_88, C_90]: (k2_zfmisc_1(k1_tarski(A_88), k2_tarski(C_90, C_90))=k1_tarski(k4_tarski(A_88, C_90)))), inference(superposition, [status(thm), theory('equality')], [c_426, c_10])).
% 2.26/1.31  tff(c_473, plain, (![A_91, C_92]: (k2_zfmisc_1(k1_tarski(A_91), k1_tarski(C_92))=k1_tarski(k4_tarski(A_91, C_92)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_448])).
% 2.26/1.31  tff(c_20, plain, (![A_16, B_17]: (~r1_tarski(A_16, k2_zfmisc_1(B_17, A_16)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.31  tff(c_479, plain, (![C_92, A_91]: (~r1_tarski(k1_tarski(C_92), k1_tarski(k4_tarski(A_91, C_92))) | k1_tarski(C_92)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_473, c_20])).
% 2.26/1.31  tff(c_553, plain, (![C_96, A_97]: (~r1_tarski(k1_tarski(C_96), k1_tarski(k4_tarski(A_97, C_96))))), inference(negUnitSimplification, [status(thm)], [c_97, c_479])).
% 2.26/1.31  tff(c_556, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_334, c_553])).
% 2.26/1.31  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_556])).
% 2.26/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.31  
% 2.26/1.31  Inference rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Ref     : 0
% 2.26/1.31  #Sup     : 130
% 2.26/1.31  #Fact    : 0
% 2.26/1.31  #Define  : 0
% 2.26/1.31  #Split   : 1
% 2.26/1.31  #Chain   : 0
% 2.26/1.31  #Close   : 0
% 2.26/1.31  
% 2.26/1.31  Ordering : KBO
% 2.26/1.31  
% 2.26/1.31  Simplification rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Subsume      : 0
% 2.26/1.31  #Demod        : 41
% 2.26/1.31  #Tautology    : 87
% 2.26/1.31  #SimpNegUnit  : 8
% 2.26/1.31  #BackRed      : 4
% 2.26/1.31  
% 2.26/1.31  #Partial instantiations: 0
% 2.26/1.31  #Strategies tried      : 1
% 2.26/1.31  
% 2.26/1.31  Timing (in seconds)
% 2.26/1.31  ----------------------
% 2.26/1.31  Preprocessing        : 0.30
% 2.26/1.31  Parsing              : 0.17
% 2.26/1.31  CNF conversion       : 0.02
% 2.26/1.31  Main loop            : 0.24
% 2.26/1.31  Inferencing          : 0.10
% 2.26/1.31  Reduction            : 0.08
% 2.26/1.31  Demodulation         : 0.06
% 2.26/1.31  BG Simplification    : 0.02
% 2.26/1.31  Subsumption          : 0.03
% 2.26/1.31  Abstraction          : 0.02
% 2.26/1.31  MUC search           : 0.00
% 2.26/1.31  Cooper               : 0.00
% 2.26/1.31  Total                : 0.57
% 2.26/1.31  Index Insertion      : 0.00
% 2.26/1.31  Index Deletion       : 0.00
% 2.26/1.31  Index Matching       : 0.00
% 2.26/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
