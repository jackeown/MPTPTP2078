%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:44 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 107 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 ( 133 expanded)
%              Number of equality atoms :   23 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_22,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_119,plain,(
    ! [A_42,B_43] : r1_tarski(A_42,k2_xboole_0(B_43,A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_24])).

tff(c_128,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_119])).

tff(c_310,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_314,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(resolution,[status(thm)],[c_128,c_310])).

tff(c_328,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_314])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_167,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_194,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_167])).

tff(c_344,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_194])).

tff(c_64,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_24])).

tff(c_318,plain,
    ( k2_tarski('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_310])).

tff(c_332,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_318])).

tff(c_361,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_332])).

tff(c_34,plain,(
    ! [D_24,B_20] : r2_hidden(D_24,k2_tarski(D_24,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_371,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_34])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_520,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,B_79)
      | ~ r2_hidden(C_80,A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_782,plain,(
    ! [C_108,B_109,A_110] :
      ( ~ r2_hidden(C_108,B_109)
      | ~ r2_hidden(C_108,A_110)
      | k4_xboole_0(A_110,B_109) != A_110 ) ),
    inference(resolution,[status(thm)],[c_28,c_520])).

tff(c_801,plain,(
    ! [A_111] :
      ( ~ r2_hidden('#skF_4',A_111)
      | k4_xboole_0(A_111,'#skF_6') != A_111 ) ),
    inference(resolution,[status(thm)],[c_371,c_782])).

tff(c_804,plain,(
    k4_xboole_0('#skF_6','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_371,c_801])).

tff(c_816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.39  
% 2.63/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.63/1.39  
% 2.63/1.39  %Foreground sorts:
% 2.63/1.39  
% 2.63/1.39  
% 2.63/1.39  %Background operators:
% 2.63/1.39  
% 2.63/1.39  
% 2.63/1.39  %Foreground operators:
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.39  
% 2.63/1.40  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.63/1.40  tff(f_84, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.63/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.63/1.40  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.63/1.40  tff(f_51, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.63/1.40  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.63/1.40  tff(f_74, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.63/1.40  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.63/1.40  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.63/1.40  tff(c_22, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.40  tff(c_54, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.63/1.40  tff(c_68, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.40  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.63/1.40  tff(c_119, plain, (![A_42, B_43]: (r1_tarski(A_42, k2_xboole_0(B_43, A_42)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_24])).
% 2.63/1.40  tff(c_128, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_119])).
% 2.63/1.40  tff(c_310, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.63/1.40  tff(c_314, plain, (k1_xboole_0='#skF_6' | ~r1_tarski(k1_xboole_0, '#skF_6')), inference(resolution, [status(thm)], [c_128, c_310])).
% 2.63/1.40  tff(c_328, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_314])).
% 2.63/1.40  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.63/1.40  tff(c_167, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.40  tff(c_194, plain, (![B_9]: (k4_xboole_0(B_9, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_167])).
% 2.63/1.40  tff(c_344, plain, (![B_9]: (k4_xboole_0(B_9, B_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_328, c_194])).
% 2.63/1.40  tff(c_64, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_24])).
% 2.63/1.40  tff(c_318, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_310])).
% 2.63/1.40  tff(c_332, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_318])).
% 2.63/1.40  tff(c_361, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_328, c_332])).
% 2.63/1.40  tff(c_34, plain, (![D_24, B_20]: (r2_hidden(D_24, k2_tarski(D_24, B_20)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.63/1.40  tff(c_371, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_361, c_34])).
% 2.63/1.40  tff(c_28, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.40  tff(c_520, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, B_79) | ~r2_hidden(C_80, A_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.40  tff(c_782, plain, (![C_108, B_109, A_110]: (~r2_hidden(C_108, B_109) | ~r2_hidden(C_108, A_110) | k4_xboole_0(A_110, B_109)!=A_110)), inference(resolution, [status(thm)], [c_28, c_520])).
% 2.63/1.40  tff(c_801, plain, (![A_111]: (~r2_hidden('#skF_4', A_111) | k4_xboole_0(A_111, '#skF_6')!=A_111)), inference(resolution, [status(thm)], [c_371, c_782])).
% 2.63/1.40  tff(c_804, plain, (k4_xboole_0('#skF_6', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_371, c_801])).
% 2.63/1.40  tff(c_816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_804])).
% 2.63/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.40  
% 2.63/1.40  Inference rules
% 2.63/1.40  ----------------------
% 2.63/1.40  #Ref     : 0
% 2.63/1.40  #Sup     : 186
% 2.63/1.40  #Fact    : 0
% 2.63/1.40  #Define  : 0
% 2.63/1.40  #Split   : 2
% 2.63/1.40  #Chain   : 0
% 2.63/1.40  #Close   : 0
% 2.63/1.40  
% 2.63/1.40  Ordering : KBO
% 2.63/1.40  
% 2.63/1.40  Simplification rules
% 2.63/1.40  ----------------------
% 2.63/1.40  #Subsume      : 15
% 2.63/1.40  #Demod        : 80
% 2.63/1.40  #Tautology    : 122
% 2.63/1.40  #SimpNegUnit  : 0
% 2.63/1.40  #BackRed      : 13
% 2.63/1.40  
% 2.63/1.40  #Partial instantiations: 0
% 2.63/1.40  #Strategies tried      : 1
% 2.63/1.40  
% 2.63/1.40  Timing (in seconds)
% 2.63/1.40  ----------------------
% 2.63/1.41  Preprocessing        : 0.32
% 2.63/1.41  Parsing              : 0.17
% 2.63/1.41  CNF conversion       : 0.02
% 2.63/1.41  Main loop            : 0.32
% 2.63/1.41  Inferencing          : 0.11
% 2.63/1.41  Reduction            : 0.11
% 2.63/1.41  Demodulation         : 0.08
% 2.63/1.41  BG Simplification    : 0.02
% 2.63/1.41  Subsumption          : 0.06
% 2.63/1.41  Abstraction          : 0.02
% 2.63/1.41  MUC search           : 0.00
% 2.63/1.41  Cooper               : 0.00
% 2.63/1.41  Total                : 0.67
% 2.63/1.41  Index Insertion      : 0.00
% 2.63/1.41  Index Deletion       : 0.00
% 2.63/1.41  Index Matching       : 0.00
% 2.63/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
