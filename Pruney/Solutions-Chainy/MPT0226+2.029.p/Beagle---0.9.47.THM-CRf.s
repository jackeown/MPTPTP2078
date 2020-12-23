%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:41 EST 2020

% Result     : Theorem 12.67s
% Output     : CNFRefutation 12.67s
% Verified   : 
% Statistics : Number of formulae       :   59 (  70 expanded)
%              Number of leaves         :   32 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 (  74 expanded)
%              Number of equality atoms :   40 (  57 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_68,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_210,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [E_22,A_16,B_17] : r2_hidden(E_22,k1_enumset1(A_16,B_17,E_22)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_228,plain,(
    ! [B_68,A_69] : r2_hidden(B_68,k2_tarski(A_69,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_32])).

tff(c_231,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_228])).

tff(c_24,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [B_54,A_55] : k5_xboole_0(B_54,A_55) = k5_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_55] : k5_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_24])).

tff(c_28,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_277,plain,(
    ! [A_85,B_86,C_87] : k5_xboole_0(k5_xboole_0(A_85,B_86),C_87) = k5_xboole_0(A_85,k5_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_341,plain,(
    ! [A_15,C_87] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_87)) = k5_xboole_0(k1_xboole_0,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_277])).

tff(c_364,plain,(
    ! [A_91,C_92] : k5_xboole_0(A_91,k5_xboole_0(A_91,C_92)) = C_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_341])).

tff(c_762,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k3_xboole_0(A_112,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_364])).

tff(c_805,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k5_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_762])).

tff(c_812,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_805])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1056,plain,(
    ! [D_128] :
      ( r2_hidden(D_128,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_128,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_6])).

tff(c_1061,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_231,c_1056])).

tff(c_56,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_731,plain,(
    ! [E_103,C_104,B_105,A_106] :
      ( E_103 = C_104
      | E_103 = B_105
      | E_103 = A_106
      | ~ r2_hidden(E_103,k1_enumset1(A_106,B_105,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20592,plain,(
    ! [E_306,B_307,A_308] :
      ( E_306 = B_307
      | E_306 = A_308
      | E_306 = A_308
      | ~ r2_hidden(E_306,k2_tarski(A_308,B_307)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_731])).

tff(c_20681,plain,(
    ! [E_309,A_310] :
      ( E_309 = A_310
      | E_309 = A_310
      | E_309 = A_310
      | ~ r2_hidden(E_309,k1_tarski(A_310)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_20592])).

tff(c_20777,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1061,c_20681])).

tff(c_20810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_68,c_20777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:24:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.67/5.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.67/5.72  
% 12.67/5.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.67/5.73  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 12.67/5.73  
% 12.67/5.73  %Foreground sorts:
% 12.67/5.73  
% 12.67/5.73  
% 12.67/5.73  %Background operators:
% 12.67/5.73  
% 12.67/5.73  
% 12.67/5.73  %Foreground operators:
% 12.67/5.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.67/5.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.67/5.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.67/5.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.67/5.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.67/5.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.67/5.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.67/5.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.67/5.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.67/5.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.67/5.73  tff('#skF_5', type, '#skF_5': $i).
% 12.67/5.73  tff('#skF_6', type, '#skF_6': $i).
% 12.67/5.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.67/5.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.67/5.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.67/5.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 12.67/5.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.67/5.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.67/5.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.67/5.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.67/5.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 12.67/5.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.67/5.73  
% 12.67/5.74  tff(f_78, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 12.67/5.74  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 12.67/5.74  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 12.67/5.74  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 12.67/5.74  tff(f_40, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.67/5.74  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.67/5.74  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 12.67/5.74  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.67/5.74  tff(f_42, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.67/5.74  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 12.67/5.74  tff(c_68, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.67/5.74  tff(c_54, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.67/5.74  tff(c_210, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.67/5.74  tff(c_32, plain, (![E_22, A_16, B_17]: (r2_hidden(E_22, k1_enumset1(A_16, B_17, E_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.67/5.74  tff(c_228, plain, (![B_68, A_69]: (r2_hidden(B_68, k2_tarski(A_69, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_32])).
% 12.67/5.74  tff(c_231, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_228])).
% 12.67/5.74  tff(c_24, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.67/5.74  tff(c_70, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.67/5.74  tff(c_22, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.67/5.74  tff(c_110, plain, (![B_54, A_55]: (k5_xboole_0(B_54, A_55)=k5_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.67/5.74  tff(c_126, plain, (![A_55]: (k5_xboole_0(k1_xboole_0, A_55)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_110, c_24])).
% 12.67/5.74  tff(c_28, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.67/5.74  tff(c_277, plain, (![A_85, B_86, C_87]: (k5_xboole_0(k5_xboole_0(A_85, B_86), C_87)=k5_xboole_0(A_85, k5_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.67/5.74  tff(c_341, plain, (![A_15, C_87]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_87))=k5_xboole_0(k1_xboole_0, C_87))), inference(superposition, [status(thm), theory('equality')], [c_28, c_277])).
% 12.67/5.74  tff(c_364, plain, (![A_91, C_92]: (k5_xboole_0(A_91, k5_xboole_0(A_91, C_92))=C_92)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_341])).
% 12.67/5.74  tff(c_762, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k3_xboole_0(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_22, c_364])).
% 12.67/5.74  tff(c_805, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k5_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_762])).
% 12.67/5.74  tff(c_812, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_805])).
% 12.67/5.74  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.67/5.74  tff(c_1056, plain, (![D_128]: (r2_hidden(D_128, k1_tarski('#skF_6')) | ~r2_hidden(D_128, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_812, c_6])).
% 12.67/5.74  tff(c_1061, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_231, c_1056])).
% 12.67/5.74  tff(c_56, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.67/5.74  tff(c_731, plain, (![E_103, C_104, B_105, A_106]: (E_103=C_104 | E_103=B_105 | E_103=A_106 | ~r2_hidden(E_103, k1_enumset1(A_106, B_105, C_104)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.67/5.74  tff(c_20592, plain, (![E_306, B_307, A_308]: (E_306=B_307 | E_306=A_308 | E_306=A_308 | ~r2_hidden(E_306, k2_tarski(A_308, B_307)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_731])).
% 12.67/5.74  tff(c_20681, plain, (![E_309, A_310]: (E_309=A_310 | E_309=A_310 | E_309=A_310 | ~r2_hidden(E_309, k1_tarski(A_310)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_20592])).
% 12.67/5.74  tff(c_20777, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1061, c_20681])).
% 12.67/5.74  tff(c_20810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_68, c_20777])).
% 12.67/5.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.67/5.74  
% 12.67/5.74  Inference rules
% 12.67/5.74  ----------------------
% 12.67/5.74  #Ref     : 0
% 12.67/5.74  #Sup     : 5256
% 12.67/5.74  #Fact    : 0
% 12.67/5.74  #Define  : 0
% 12.67/5.74  #Split   : 1
% 12.67/5.74  #Chain   : 0
% 12.67/5.74  #Close   : 0
% 12.67/5.74  
% 12.67/5.74  Ordering : KBO
% 12.67/5.74  
% 12.67/5.74  Simplification rules
% 12.67/5.74  ----------------------
% 12.67/5.74  #Subsume      : 633
% 12.67/5.74  #Demod        : 8017
% 12.67/5.74  #Tautology    : 2301
% 12.67/5.74  #SimpNegUnit  : 1
% 12.67/5.74  #BackRed      : 1
% 12.67/5.74  
% 12.67/5.74  #Partial instantiations: 0
% 12.67/5.74  #Strategies tried      : 1
% 12.67/5.74  
% 12.67/5.74  Timing (in seconds)
% 12.67/5.74  ----------------------
% 12.67/5.74  Preprocessing        : 0.34
% 12.67/5.74  Parsing              : 0.16
% 12.67/5.74  CNF conversion       : 0.03
% 12.67/5.74  Main loop            : 4.63
% 12.67/5.74  Inferencing          : 0.69
% 12.67/5.74  Reduction            : 3.30
% 12.67/5.74  Demodulation         : 3.14
% 12.67/5.74  BG Simplification    : 0.10
% 12.67/5.74  Subsumption          : 0.40
% 12.67/5.74  Abstraction          : 0.17
% 12.67/5.74  MUC search           : 0.00
% 12.67/5.74  Cooper               : 0.00
% 12.67/5.74  Total                : 5.00
% 12.67/5.74  Index Insertion      : 0.00
% 12.67/5.74  Index Deletion       : 0.00
% 12.67/5.74  Index Matching       : 0.00
% 12.67/5.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
