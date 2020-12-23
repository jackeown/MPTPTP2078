%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:15 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 114 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 147 expanded)
%              Number of equality atoms :   24 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_48,plain,(
    ! [D_26,A_21] : r2_hidden(D_26,k2_tarski(A_21,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_153,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_153])).

tff(c_182,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_200,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) = k4_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_182])).

tff(c_206,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_200])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_259,plain,(
    ! [D_70,A_71,B_72] :
      ( r2_hidden(D_70,A_71)
      | ~ r2_hidden(D_70,k3_xboole_0(A_71,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_8])).

tff(c_265,plain,(
    ! [D_70,A_1,B_2] :
      ( r2_hidden(D_70,A_1)
      | ~ r2_hidden(D_70,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_424,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_86,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_265])).

tff(c_437,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_424])).

tff(c_34,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_442,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_437,c_34])).

tff(c_70,plain,(
    '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_449,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_70])).

tff(c_50,plain,(
    ! [D_26,B_22] : r2_hidden(D_26,k2_tarski(D_26,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_438,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_50,c_424])).

tff(c_650,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_438])).

tff(c_653,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_650,c_34])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.41  
% 2.68/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.68/1.41  
% 2.68/1.41  %Foreground sorts:
% 2.68/1.41  
% 2.68/1.41  
% 2.68/1.41  %Background operators:
% 2.68/1.41  
% 2.68/1.41  
% 2.68/1.41  %Foreground operators:
% 2.68/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.68/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.68/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.68/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.68/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.68/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.68/1.41  
% 2.68/1.42  tff(f_65, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.68/1.42  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.68/1.42  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.68/1.42  tff(f_76, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.68/1.42  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.68/1.42  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.68/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.68/1.42  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.68/1.42  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.68/1.42  tff(c_48, plain, (![D_26, A_21]: (r2_hidden(D_26, k2_tarski(A_21, D_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.42  tff(c_28, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.68/1.42  tff(c_133, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.42  tff(c_137, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(resolution, [status(thm)], [c_28, c_133])).
% 2.68/1.42  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.68/1.42  tff(c_153, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.42  tff(c_161, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_153])).
% 2.68/1.42  tff(c_182, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.42  tff(c_200, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))=k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_161, c_182])).
% 2.68/1.42  tff(c_206, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_200])).
% 2.68/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.42  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.42  tff(c_259, plain, (![D_70, A_71, B_72]: (r2_hidden(D_70, A_71) | ~r2_hidden(D_70, k3_xboole_0(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_182, c_8])).
% 2.68/1.42  tff(c_265, plain, (![D_70, A_1, B_2]: (r2_hidden(D_70, A_1) | ~r2_hidden(D_70, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_259])).
% 2.68/1.42  tff(c_424, plain, (![D_86]: (r2_hidden(D_86, k1_tarski('#skF_9')) | ~r2_hidden(D_86, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_206, c_265])).
% 2.68/1.42  tff(c_437, plain, (r2_hidden('#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_424])).
% 2.68/1.42  tff(c_34, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.42  tff(c_442, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_437, c_34])).
% 2.68/1.42  tff(c_70, plain, ('#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.68/1.42  tff(c_449, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_70])).
% 2.68/1.42  tff(c_50, plain, (![D_26, B_22]: (r2_hidden(D_26, k2_tarski(D_26, B_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.42  tff(c_438, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_50, c_424])).
% 2.68/1.42  tff(c_650, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_438])).
% 2.68/1.42  tff(c_653, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_650, c_34])).
% 2.68/1.42  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_449, c_653])).
% 2.68/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  Inference rules
% 2.68/1.42  ----------------------
% 2.68/1.42  #Ref     : 0
% 2.68/1.42  #Sup     : 118
% 2.68/1.42  #Fact    : 0
% 2.68/1.42  #Define  : 0
% 2.68/1.42  #Split   : 0
% 2.68/1.42  #Chain   : 0
% 2.68/1.42  #Close   : 0
% 2.68/1.42  
% 2.68/1.42  Ordering : KBO
% 2.68/1.42  
% 2.68/1.42  Simplification rules
% 2.68/1.42  ----------------------
% 2.68/1.42  #Subsume      : 17
% 2.68/1.42  #Demod        : 34
% 2.68/1.42  #Tautology    : 54
% 2.68/1.42  #SimpNegUnit  : 1
% 2.68/1.42  #BackRed      : 7
% 2.68/1.42  
% 2.68/1.42  #Partial instantiations: 544
% 2.68/1.42  #Strategies tried      : 1
% 2.68/1.42  
% 2.68/1.42  Timing (in seconds)
% 2.68/1.42  ----------------------
% 2.68/1.42  Preprocessing        : 0.33
% 2.68/1.42  Parsing              : 0.17
% 2.68/1.42  CNF conversion       : 0.03
% 2.68/1.42  Main loop            : 0.32
% 2.68/1.42  Inferencing          : 0.14
% 2.68/1.42  Reduction            : 0.09
% 2.68/1.42  Demodulation         : 0.07
% 2.68/1.42  BG Simplification    : 0.02
% 2.68/1.42  Subsumption          : 0.05
% 2.68/1.42  Abstraction          : 0.01
% 2.68/1.42  MUC search           : 0.00
% 2.68/1.42  Cooper               : 0.00
% 2.68/1.43  Total                : 0.68
% 2.68/1.43  Index Insertion      : 0.00
% 2.68/1.43  Index Deletion       : 0.00
% 2.68/1.43  Index Matching       : 0.00
% 2.68/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
