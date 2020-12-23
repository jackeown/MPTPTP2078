%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:20 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   58 (  85 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 ( 101 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_70,plain,(
    k2_tarski('#skF_3','#skF_4') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_497,plain,(
    ! [B_81,A_82] :
      ( k1_tarski(B_81) = A_82
      | k1_xboole_0 = A_82
      | ~ r1_tarski(A_82,k1_tarski(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_500,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_497])).

tff(c_519,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_500])).

tff(c_235,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [E_23,A_17,B_18] : r2_hidden(E_23,k1_enumset1(A_17,B_18,E_23)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_247,plain,(
    ! [B_60,A_59] : r2_hidden(B_60,k2_tarski(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_34])).

tff(c_540,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_247])).

tff(c_30,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_125,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(A_54,B_55) = B_55
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_342,plain,(
    ! [A_71,B_72] : k2_xboole_0(k4_xboole_0(A_71,B_72),A_71) = A_71 ),
    inference(resolution,[status(thm)],[c_30,c_125])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_155,plain,(
    ! [A_57] : k2_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_165,plain,(
    ! [A_57] : k2_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_2])).

tff(c_349,plain,(
    ! [B_72] : k4_xboole_0(k1_xboole_0,B_72) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_165])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_283,plain,(
    ! [A_66,B_67] : k2_xboole_0(k3_xboole_0(A_66,B_67),A_66) = A_66 ),
    inference(resolution,[status(thm)],[c_26,c_125])).

tff(c_323,plain,(
    ! [B_70] : k3_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_165])).

tff(c_22,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_328,plain,(
    ! [B_70] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_22])).

tff(c_492,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_328])).

tff(c_617,plain,(
    ! [A_103,C_104,B_105] :
      ( ~ r2_hidden(A_103,C_104)
      | ~ r2_hidden(A_103,B_105)
      | ~ r2_hidden(A_103,k5_xboole_0(B_105,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_632,plain,(
    ! [A_106] :
      ( ~ r2_hidden(A_106,k1_xboole_0)
      | ~ r2_hidden(A_106,k1_xboole_0)
      | ~ r2_hidden(A_106,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_617])).

tff(c_634,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_540,c_632])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:38:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.87  
% 3.09/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.87  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.09/1.87  
% 3.09/1.87  %Foreground sorts:
% 3.09/1.87  
% 3.09/1.87  
% 3.09/1.87  %Background operators:
% 3.09/1.87  
% 3.09/1.87  
% 3.09/1.87  %Foreground operators:
% 3.09/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.09/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.87  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.09/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.87  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.87  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.09/1.87  
% 3.09/1.89  tff(f_86, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 3.09/1.89  tff(f_81, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.09/1.89  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.09/1.89  tff(f_67, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.09/1.89  tff(f_52, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.09/1.89  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.09/1.89  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.09/1.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.09/1.89  tff(f_48, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.09/1.89  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.09/1.89  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.09/1.89  tff(c_70, plain, (k2_tarski('#skF_3', '#skF_4')!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.89  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.89  tff(c_497, plain, (![B_81, A_82]: (k1_tarski(B_81)=A_82 | k1_xboole_0=A_82 | ~r1_tarski(A_82, k1_tarski(B_81)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.09/1.89  tff(c_500, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_497])).
% 3.09/1.89  tff(c_519, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_500])).
% 3.09/1.89  tff(c_235, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.09/1.89  tff(c_34, plain, (![E_23, A_17, B_18]: (r2_hidden(E_23, k1_enumset1(A_17, B_18, E_23)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.09/1.89  tff(c_247, plain, (![B_60, A_59]: (r2_hidden(B_60, k2_tarski(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_34])).
% 3.09/1.89  tff(c_540, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_519, c_247])).
% 3.09/1.89  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.09/1.89  tff(c_125, plain, (![A_54, B_55]: (k2_xboole_0(A_54, B_55)=B_55 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.09/1.89  tff(c_342, plain, (![A_71, B_72]: (k2_xboole_0(k4_xboole_0(A_71, B_72), A_71)=A_71)), inference(resolution, [status(thm)], [c_30, c_125])).
% 3.09/1.89  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.09/1.89  tff(c_155, plain, (![A_57]: (k2_xboole_0(k1_xboole_0, A_57)=A_57)), inference(resolution, [status(thm)], [c_28, c_125])).
% 3.09/1.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.89  tff(c_165, plain, (![A_57]: (k2_xboole_0(A_57, k1_xboole_0)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_155, c_2])).
% 3.09/1.89  tff(c_349, plain, (![B_72]: (k4_xboole_0(k1_xboole_0, B_72)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_342, c_165])).
% 3.09/1.89  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.89  tff(c_283, plain, (![A_66, B_67]: (k2_xboole_0(k3_xboole_0(A_66, B_67), A_66)=A_66)), inference(resolution, [status(thm)], [c_26, c_125])).
% 3.09/1.89  tff(c_323, plain, (![B_70]: (k3_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_283, c_165])).
% 3.09/1.89  tff(c_22, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.09/1.89  tff(c_328, plain, (![B_70]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_323, c_22])).
% 3.09/1.89  tff(c_492, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_349, c_328])).
% 3.09/1.89  tff(c_617, plain, (![A_103, C_104, B_105]: (~r2_hidden(A_103, C_104) | ~r2_hidden(A_103, B_105) | ~r2_hidden(A_103, k5_xboole_0(B_105, C_104)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.09/1.89  tff(c_632, plain, (![A_106]: (~r2_hidden(A_106, k1_xboole_0) | ~r2_hidden(A_106, k1_xboole_0) | ~r2_hidden(A_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_492, c_617])).
% 3.09/1.89  tff(c_634, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_540, c_632])).
% 3.09/1.89  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_540, c_634])).
% 3.09/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.89  
% 3.09/1.89  Inference rules
% 3.09/1.89  ----------------------
% 3.09/1.89  #Ref     : 0
% 3.09/1.89  #Sup     : 129
% 3.09/1.89  #Fact    : 0
% 3.09/1.89  #Define  : 0
% 3.09/1.89  #Split   : 0
% 3.09/1.89  #Chain   : 0
% 3.09/1.89  #Close   : 0
% 3.09/1.89  
% 3.09/1.89  Ordering : KBO
% 3.09/1.89  
% 3.09/1.89  Simplification rules
% 3.09/1.89  ----------------------
% 3.09/1.89  #Subsume      : 0
% 3.09/1.89  #Demod        : 56
% 3.09/1.89  #Tautology    : 106
% 3.09/1.89  #SimpNegUnit  : 2
% 3.09/1.89  #BackRed      : 5
% 3.09/1.89  
% 3.09/1.89  #Partial instantiations: 0
% 3.09/1.89  #Strategies tried      : 1
% 3.09/1.89  
% 3.09/1.89  Timing (in seconds)
% 3.09/1.89  ----------------------
% 3.09/1.89  Preprocessing        : 0.55
% 3.09/1.89  Parsing              : 0.27
% 3.09/1.89  CNF conversion       : 0.04
% 3.09/1.89  Main loop            : 0.42
% 3.09/1.89  Inferencing          : 0.14
% 3.09/1.89  Reduction            : 0.15
% 3.09/1.89  Demodulation         : 0.11
% 3.09/1.89  BG Simplification    : 0.03
% 3.09/1.89  Subsumption          : 0.07
% 3.09/1.89  Abstraction          : 0.02
% 3.09/1.89  MUC search           : 0.00
% 3.09/1.89  Cooper               : 0.00
% 3.09/1.89  Total                : 1.02
% 3.09/1.89  Index Insertion      : 0.00
% 3.09/1.89  Index Deletion       : 0.00
% 3.09/1.89  Index Matching       : 0.00
% 3.09/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
