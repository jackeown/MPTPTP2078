%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:20 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   55 (  59 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  49 expanded)
%              Number of equality atoms :   32 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1002,plain,(
    ! [A_1885,B_1886,C_1887,D_1888] : k2_xboole_0(k1_enumset1(A_1885,B_1886,C_1887),k1_tarski(D_1888)) = k2_enumset1(A_1885,B_1886,C_1887,D_1888) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1052,plain,(
    ! [A_24,B_25,D_1888] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(D_1888)) = k2_enumset1(A_24,A_24,B_25,D_1888) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1002])).

tff(c_1087,plain,(
    ! [A_1995,B_1996,D_1997] : k2_xboole_0(k2_tarski(A_1995,B_1996),k1_tarski(D_1997)) = k1_enumset1(A_1995,B_1996,D_1997) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1052])).

tff(c_1137,plain,(
    ! [A_23,D_1997] : k2_xboole_0(k1_tarski(A_23),k1_tarski(D_1997)) = k1_enumset1(A_23,A_23,D_1997) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1087])).

tff(c_1141,plain,(
    ! [A_2050,D_2051] : k2_xboole_0(k1_tarski(A_2050),k1_tarski(D_2051)) = k2_tarski(A_2050,D_2051) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1137])).

tff(c_62,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_81,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [B_60,A_61] : r1_tarski(k3_xboole_0(B_60,A_61),A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_6])).

tff(c_172,plain,(
    ! [A_72,B_73] :
      ( k2_xboole_0(A_72,B_73) = B_73
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_233,plain,(
    ! [B_80,A_81] : k2_xboole_0(k3_xboole_0(B_80,A_81),A_81) = A_81 ),
    inference(resolution,[status(thm)],[c_96,c_172])).

tff(c_253,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_233])).

tff(c_1147,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1141,c_253])).

tff(c_154,plain,(
    ! [A_70,B_71] : k1_enumset1(A_70,A_70,B_71) = k2_tarski(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [E_13,B_8,C_9] : r2_hidden(E_13,k1_enumset1(E_13,B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_166,plain,(
    ! [A_70,B_71] : r2_hidden(A_70,k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_14])).

tff(c_1252,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1147,c_166])).

tff(c_32,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1281,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1252,c_32])).

tff(c_1315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:15:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.82/1.41  
% 2.82/1.41  %Foreground sorts:
% 2.82/1.41  
% 2.82/1.41  
% 2.82/1.41  %Background operators:
% 2.82/1.41  
% 2.82/1.41  
% 2.82/1.41  %Foreground operators:
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.82/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.82/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.82/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.82/1.41  
% 2.82/1.42  tff(f_76, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.82/1.42  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.82/1.42  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.82/1.42  tff(f_63, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.82/1.42  tff(f_57, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.82/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.82/1.42  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.82/1.42  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.82/1.42  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.82/1.42  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.82/1.42  tff(c_60, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.82/1.42  tff(c_48, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.82/1.42  tff(c_46, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.42  tff(c_50, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.82/1.42  tff(c_1002, plain, (![A_1885, B_1886, C_1887, D_1888]: (k2_xboole_0(k1_enumset1(A_1885, B_1886, C_1887), k1_tarski(D_1888))=k2_enumset1(A_1885, B_1886, C_1887, D_1888))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.42  tff(c_1052, plain, (![A_24, B_25, D_1888]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(D_1888))=k2_enumset1(A_24, A_24, B_25, D_1888))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1002])).
% 2.82/1.42  tff(c_1087, plain, (![A_1995, B_1996, D_1997]: (k2_xboole_0(k2_tarski(A_1995, B_1996), k1_tarski(D_1997))=k1_enumset1(A_1995, B_1996, D_1997))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1052])).
% 2.82/1.42  tff(c_1137, plain, (![A_23, D_1997]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(D_1997))=k1_enumset1(A_23, A_23, D_1997))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1087])).
% 2.82/1.42  tff(c_1141, plain, (![A_2050, D_2051]: (k2_xboole_0(k1_tarski(A_2050), k1_tarski(D_2051))=k2_tarski(A_2050, D_2051))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1137])).
% 2.82/1.42  tff(c_62, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.82/1.42  tff(c_81, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.42  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.82/1.42  tff(c_96, plain, (![B_60, A_61]: (r1_tarski(k3_xboole_0(B_60, A_61), A_61))), inference(superposition, [status(thm), theory('equality')], [c_81, c_6])).
% 2.82/1.42  tff(c_172, plain, (![A_72, B_73]: (k2_xboole_0(A_72, B_73)=B_73 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.42  tff(c_233, plain, (![B_80, A_81]: (k2_xboole_0(k3_xboole_0(B_80, A_81), A_81)=A_81)), inference(resolution, [status(thm)], [c_96, c_172])).
% 2.82/1.42  tff(c_253, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_62, c_233])).
% 2.82/1.42  tff(c_1147, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1141, c_253])).
% 2.82/1.42  tff(c_154, plain, (![A_70, B_71]: (k1_enumset1(A_70, A_70, B_71)=k2_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.82/1.42  tff(c_14, plain, (![E_13, B_8, C_9]: (r2_hidden(E_13, k1_enumset1(E_13, B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.42  tff(c_166, plain, (![A_70, B_71]: (r2_hidden(A_70, k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_14])).
% 2.82/1.42  tff(c_1252, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1147, c_166])).
% 2.82/1.42  tff(c_32, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.42  tff(c_1281, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1252, c_32])).
% 2.82/1.42  tff(c_1315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1281])).
% 2.82/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  Inference rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Ref     : 0
% 2.82/1.42  #Sup     : 138
% 2.82/1.42  #Fact    : 0
% 2.82/1.42  #Define  : 0
% 2.82/1.42  #Split   : 2
% 2.82/1.42  #Chain   : 0
% 2.82/1.42  #Close   : 0
% 2.82/1.42  
% 2.82/1.42  Ordering : KBO
% 2.82/1.42  
% 2.82/1.42  Simplification rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Subsume      : 2
% 2.82/1.42  #Demod        : 29
% 2.82/1.42  #Tautology    : 68
% 2.82/1.42  #SimpNegUnit  : 1
% 2.82/1.42  #BackRed      : 0
% 2.82/1.42  
% 2.82/1.42  #Partial instantiations: 640
% 2.82/1.42  #Strategies tried      : 1
% 2.82/1.42  
% 2.82/1.42  Timing (in seconds)
% 2.82/1.42  ----------------------
% 2.82/1.42  Preprocessing        : 0.32
% 2.82/1.42  Parsing              : 0.17
% 2.82/1.42  CNF conversion       : 0.02
% 2.82/1.42  Main loop            : 0.36
% 2.82/1.42  Inferencing          : 0.19
% 2.82/1.42  Reduction            : 0.09
% 2.82/1.42  Demodulation         : 0.07
% 2.82/1.42  BG Simplification    : 0.02
% 2.82/1.42  Subsumption          : 0.05
% 2.82/1.42  Abstraction          : 0.01
% 2.82/1.42  MUC search           : 0.00
% 2.82/1.42  Cooper               : 0.00
% 2.82/1.42  Total                : 0.71
% 2.82/1.42  Index Insertion      : 0.00
% 2.82/1.42  Index Deletion       : 0.00
% 2.82/1.42  Index Matching       : 0.00
% 2.82/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
