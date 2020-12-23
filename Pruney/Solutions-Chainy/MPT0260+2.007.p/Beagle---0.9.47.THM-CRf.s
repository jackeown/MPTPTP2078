%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:10 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   56 (  61 expanded)
%              Number of leaves         :   33 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  59 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_60,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_74,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_160,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    ! [E_27,A_21,C_23] : r2_hidden(E_27,k1_enumset1(A_21,E_27,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_169,plain,(
    ! [A_75,B_76] : r2_hidden(A_75,k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_42])).

tff(c_32,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_202,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,k3_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_205,plain,(
    ! [A_14,C_93] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_93,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_202])).

tff(c_207,plain,(
    ! [C_93] : ~ r2_hidden(C_93,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_205])).

tff(c_28,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_208,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k4_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_240,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_208])).

tff(c_244,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_240])).

tff(c_76,plain,(
    r1_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_117,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = A_72
      | ~ r1_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_136,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_117])).

tff(c_227,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),k2_tarski('#skF_6','#skF_7')) = k3_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_208])).

tff(c_303,plain,(
    k3_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_227])).

tff(c_739,plain,(
    ! [D_136,A_137,B_138] :
      ( r2_hidden(D_136,k3_xboole_0(A_137,B_138))
      | ~ r2_hidden(D_136,B_138)
      | ~ r2_hidden(D_136,A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_763,plain,(
    ! [D_136] :
      ( r2_hidden(D_136,k1_xboole_0)
      | ~ r2_hidden(D_136,'#skF_8')
      | ~ r2_hidden(D_136,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_739])).

tff(c_832,plain,(
    ! [D_141] :
      ( ~ r2_hidden(D_141,'#skF_8')
      | ~ r2_hidden(D_141,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_763])).

tff(c_840,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_169,c_832])).

tff(c_849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:07:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.57  
% 2.81/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.57  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5
% 2.81/1.57  
% 2.81/1.57  %Foreground sorts:
% 2.81/1.57  
% 2.81/1.57  
% 2.81/1.57  %Background operators:
% 2.81/1.57  
% 2.81/1.57  
% 2.81/1.57  %Foreground operators:
% 2.81/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.81/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.57  tff('#skF_7', type, '#skF_7': $i).
% 2.81/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.57  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.81/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.81/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.57  tff('#skF_8', type, '#skF_8': $i).
% 2.81/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.81/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.57  
% 2.81/1.58  tff(f_97, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.81/1.58  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.81/1.58  tff(f_79, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.81/1.58  tff(f_60, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.81/1.58  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.81/1.58  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.81/1.58  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.81/1.58  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.81/1.58  tff(f_64, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.81/1.58  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.81/1.58  tff(c_74, plain, (r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.81/1.58  tff(c_160, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.81/1.58  tff(c_42, plain, (![E_27, A_21, C_23]: (r2_hidden(E_27, k1_enumset1(A_21, E_27, C_23)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.81/1.58  tff(c_169, plain, (![A_75, B_76]: (r2_hidden(A_75, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_42])).
% 2.81/1.58  tff(c_32, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.81/1.58  tff(c_26, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.58  tff(c_202, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, k3_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.81/1.58  tff(c_205, plain, (![A_14, C_93]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_202])).
% 2.81/1.58  tff(c_207, plain, (![C_93]: (~r2_hidden(C_93, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_205])).
% 2.81/1.58  tff(c_28, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.81/1.58  tff(c_208, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k4_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.81/1.58  tff(c_240, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_208])).
% 2.81/1.58  tff(c_244, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_240])).
% 2.81/1.58  tff(c_76, plain, (r1_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.81/1.58  tff(c_117, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=A_72 | ~r1_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.58  tff(c_136, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k2_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_76, c_117])).
% 2.81/1.58  tff(c_227, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), k2_tarski('#skF_6', '#skF_7'))=k3_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_136, c_208])).
% 2.81/1.58  tff(c_303, plain, (k3_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_244, c_227])).
% 2.81/1.58  tff(c_739, plain, (![D_136, A_137, B_138]: (r2_hidden(D_136, k3_xboole_0(A_137, B_138)) | ~r2_hidden(D_136, B_138) | ~r2_hidden(D_136, A_137))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.81/1.58  tff(c_763, plain, (![D_136]: (r2_hidden(D_136, k1_xboole_0) | ~r2_hidden(D_136, '#skF_8') | ~r2_hidden(D_136, k2_tarski('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_303, c_739])).
% 2.81/1.58  tff(c_832, plain, (![D_141]: (~r2_hidden(D_141, '#skF_8') | ~r2_hidden(D_141, k2_tarski('#skF_6', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_207, c_763])).
% 2.81/1.58  tff(c_840, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_169, c_832])).
% 2.81/1.58  tff(c_849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_840])).
% 2.81/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.58  
% 2.81/1.58  Inference rules
% 2.81/1.58  ----------------------
% 2.81/1.58  #Ref     : 0
% 2.81/1.58  #Sup     : 191
% 2.81/1.58  #Fact    : 0
% 2.81/1.58  #Define  : 0
% 2.81/1.58  #Split   : 0
% 2.81/1.58  #Chain   : 0
% 2.81/1.58  #Close   : 0
% 2.81/1.58  
% 2.81/1.58  Ordering : KBO
% 2.81/1.58  
% 2.81/1.58  Simplification rules
% 2.81/1.58  ----------------------
% 2.81/1.58  #Subsume      : 55
% 2.81/1.58  #Demod        : 38
% 2.81/1.58  #Tautology    : 93
% 2.81/1.58  #SimpNegUnit  : 14
% 2.81/1.58  #BackRed      : 0
% 2.81/1.58  
% 2.81/1.58  #Partial instantiations: 0
% 2.81/1.58  #Strategies tried      : 1
% 2.81/1.58  
% 2.81/1.58  Timing (in seconds)
% 2.81/1.59  ----------------------
% 2.81/1.59  Preprocessing        : 0.37
% 2.81/1.59  Parsing              : 0.18
% 2.81/1.59  CNF conversion       : 0.03
% 2.81/1.59  Main loop            : 0.33
% 2.81/1.59  Inferencing          : 0.11
% 2.81/1.59  Reduction            : 0.11
% 2.81/1.59  Demodulation         : 0.08
% 2.81/1.59  BG Simplification    : 0.02
% 2.81/1.59  Subsumption          : 0.06
% 2.81/1.59  Abstraction          : 0.02
% 2.81/1.59  MUC search           : 0.00
% 2.81/1.59  Cooper               : 0.00
% 2.81/1.59  Total                : 0.73
% 2.81/1.59  Index Insertion      : 0.00
% 2.81/1.59  Index Deletion       : 0.00
% 2.81/1.59  Index Matching       : 0.00
% 2.81/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
