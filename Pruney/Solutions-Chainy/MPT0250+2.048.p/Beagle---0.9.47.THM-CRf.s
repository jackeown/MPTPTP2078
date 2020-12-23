%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:38 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   57 (  65 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  64 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_76,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_60,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_197,plain,(
    ! [A_78,B_79] : k1_enumset1(A_78,A_78,B_79) = k2_tarski(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [E_26,A_20,C_22] : r2_hidden(E_26,k1_enumset1(A_20,E_26,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_215,plain,(
    ! [A_80,B_81] : r2_hidden(A_80,k2_tarski(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_40])).

tff(c_218,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_215])).

tff(c_30,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_267,plain,(
    ! [A_100,B_101] : k5_xboole_0(k5_xboole_0(A_100,B_101),k3_xboole_0(A_100,B_101)) = k2_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_915,plain,(
    ! [B_131,A_132] : k5_xboole_0(k5_xboole_0(B_131,A_132),k3_xboole_0(A_132,B_131)) = k2_xboole_0(B_131,A_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_267])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_294,plain,(
    ! [B_4,A_3] : k5_xboole_0(k5_xboole_0(B_4,A_3),k3_xboole_0(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_267])).

tff(c_933,plain,(
    ! [B_131,A_132] : k2_xboole_0(B_131,A_132) = k2_xboole_0(A_132,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_294])).

tff(c_78,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_234,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(B_91,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_244,plain,
    ( k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_234])).

tff(c_320,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_1036,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_320])).

tff(c_1040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1036])).

tff(c_1041,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1066,plain,(
    ! [D_133] :
      ( ~ r2_hidden(D_133,k1_tarski('#skF_5'))
      | r2_hidden(D_133,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_10])).

tff(c_1070,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_218,c_1066])).

tff(c_1074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.53  
% 3.14/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.53  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.14/1.53  
% 3.14/1.53  %Foreground sorts:
% 3.14/1.53  
% 3.14/1.53  
% 3.14/1.53  %Background operators:
% 3.14/1.53  
% 3.14/1.53  
% 3.14/1.53  %Foreground operators:
% 3.14/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.14/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.14/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.14/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.14/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.14/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.53  
% 3.14/1.54  tff(f_86, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.14/1.54  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.14/1.54  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.14/1.54  tff(f_65, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.14/1.54  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.14/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.14/1.54  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.14/1.54  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.14/1.54  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.54  tff(f_38, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.14/1.54  tff(c_76, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.54  tff(c_60, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.14/1.54  tff(c_197, plain, (![A_78, B_79]: (k1_enumset1(A_78, A_78, B_79)=k2_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.14/1.54  tff(c_40, plain, (![E_26, A_20, C_22]: (r2_hidden(E_26, k1_enumset1(A_20, E_26, C_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.14/1.54  tff(c_215, plain, (![A_80, B_81]: (r2_hidden(A_80, k2_tarski(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_40])).
% 3.14/1.54  tff(c_218, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_215])).
% 3.14/1.54  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.14/1.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.54  tff(c_267, plain, (![A_100, B_101]: (k5_xboole_0(k5_xboole_0(A_100, B_101), k3_xboole_0(A_100, B_101))=k2_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.54  tff(c_915, plain, (![B_131, A_132]: (k5_xboole_0(k5_xboole_0(B_131, A_132), k3_xboole_0(A_132, B_131))=k2_xboole_0(B_131, A_132))), inference(superposition, [status(thm), theory('equality')], [c_2, c_267])).
% 3.14/1.54  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.54  tff(c_294, plain, (![B_4, A_3]: (k5_xboole_0(k5_xboole_0(B_4, A_3), k3_xboole_0(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_267])).
% 3.14/1.54  tff(c_933, plain, (![B_131, A_132]: (k2_xboole_0(B_131, A_132)=k2_xboole_0(A_132, B_131))), inference(superposition, [status(thm), theory('equality')], [c_915, c_294])).
% 3.14/1.54  tff(c_78, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.54  tff(c_234, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(B_91, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.54  tff(c_244, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_78, c_234])).
% 3.14/1.54  tff(c_320, plain, (~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_244])).
% 3.14/1.54  tff(c_1036, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_933, c_320])).
% 3.14/1.54  tff(c_1040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1036])).
% 3.14/1.54  tff(c_1041, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_244])).
% 3.14/1.54  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.54  tff(c_1066, plain, (![D_133]: (~r2_hidden(D_133, k1_tarski('#skF_5')) | r2_hidden(D_133, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_10])).
% 3.14/1.54  tff(c_1070, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_218, c_1066])).
% 3.14/1.54  tff(c_1074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1070])).
% 3.14/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.54  
% 3.14/1.54  Inference rules
% 3.14/1.54  ----------------------
% 3.14/1.54  #Ref     : 0
% 3.14/1.54  #Sup     : 262
% 3.14/1.54  #Fact    : 0
% 3.14/1.54  #Define  : 0
% 3.14/1.54  #Split   : 1
% 3.14/1.54  #Chain   : 0
% 3.14/1.54  #Close   : 0
% 3.14/1.54  
% 3.14/1.54  Ordering : KBO
% 3.14/1.54  
% 3.14/1.54  Simplification rules
% 3.14/1.54  ----------------------
% 3.14/1.54  #Subsume      : 11
% 3.14/1.54  #Demod        : 91
% 3.14/1.54  #Tautology    : 87
% 3.14/1.54  #SimpNegUnit  : 1
% 3.14/1.54  #BackRed      : 3
% 3.14/1.54  
% 3.14/1.54  #Partial instantiations: 0
% 3.14/1.54  #Strategies tried      : 1
% 3.14/1.54  
% 3.14/1.54  Timing (in seconds)
% 3.14/1.54  ----------------------
% 3.47/1.54  Preprocessing        : 0.33
% 3.47/1.54  Parsing              : 0.16
% 3.47/1.54  CNF conversion       : 0.03
% 3.47/1.54  Main loop            : 0.43
% 3.47/1.54  Inferencing          : 0.12
% 3.47/1.54  Reduction            : 0.19
% 3.47/1.54  Demodulation         : 0.16
% 3.47/1.54  BG Simplification    : 0.03
% 3.47/1.54  Subsumption          : 0.07
% 3.47/1.54  Abstraction          : 0.03
% 3.47/1.54  MUC search           : 0.00
% 3.47/1.54  Cooper               : 0.00
% 3.47/1.54  Total                : 0.78
% 3.47/1.54  Index Insertion      : 0.00
% 3.47/1.54  Index Deletion       : 0.00
% 3.47/1.54  Index Matching       : 0.00
% 3.47/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
