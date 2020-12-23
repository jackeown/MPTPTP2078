%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:17 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   50 (  54 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  44 expanded)
%              Number of equality atoms :   32 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_770,plain,(
    ! [A_1283,B_1284,C_1285,D_1286] : k2_xboole_0(k1_enumset1(A_1283,B_1284,C_1285),k1_tarski(D_1286)) = k2_enumset1(A_1283,B_1284,C_1285,D_1286) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_824,plain,(
    ! [A_24,B_25,D_1286] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(D_1286)) = k2_enumset1(A_24,A_24,B_25,D_1286) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_770])).

tff(c_836,plain,(
    ! [A_1331,B_1332,D_1333] : k2_xboole_0(k2_tarski(A_1331,B_1332),k1_tarski(D_1333)) = k1_enumset1(A_1331,B_1332,D_1333) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_824])).

tff(c_896,plain,(
    ! [A_23,D_1333] : k2_xboole_0(k1_tarski(A_23),k1_tarski(D_1333)) = k1_enumset1(A_23,A_23,D_1333) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_836])).

tff(c_932,plain,(
    ! [A_1424,D_1425] : k2_xboole_0(k1_tarski(A_1424),k1_tarski(D_1425)) = k2_tarski(A_1424,D_1425) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_896])).

tff(c_60,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_139,plain,(
    ! [A_56,B_57] : k2_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [B_63,A_64] : k2_xboole_0(B_63,k3_xboole_0(A_64,B_63)) = B_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_139])).

tff(c_193,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_180])).

tff(c_938,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_193])).

tff(c_211,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_217,plain,(
    ! [B_66,A_65] : r2_hidden(B_66,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_10])).

tff(c_1053,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_938,c_217])).

tff(c_32,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1077,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1053,c_32])).

tff(c_1110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1077])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:42:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.45  
% 2.60/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.45  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.60/1.45  
% 2.60/1.45  %Foreground sorts:
% 2.60/1.45  
% 2.60/1.45  
% 2.60/1.45  %Background operators:
% 2.60/1.45  
% 2.60/1.45  
% 2.60/1.45  %Foreground operators:
% 2.60/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.60/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.60/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.60/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.60/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.60/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.60/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.60/1.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.60/1.45  
% 2.60/1.46  tff(f_72, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.60/1.46  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.60/1.46  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.60/1.46  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.60/1.46  tff(f_55, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.60/1.46  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.60/1.46  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.60/1.46  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.60/1.46  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.60/1.46  tff(c_58, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.60/1.46  tff(c_48, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.46  tff(c_46, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.46  tff(c_50, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.60/1.46  tff(c_770, plain, (![A_1283, B_1284, C_1285, D_1286]: (k2_xboole_0(k1_enumset1(A_1283, B_1284, C_1285), k1_tarski(D_1286))=k2_enumset1(A_1283, B_1284, C_1285, D_1286))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.60/1.46  tff(c_824, plain, (![A_24, B_25, D_1286]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(D_1286))=k2_enumset1(A_24, A_24, B_25, D_1286))), inference(superposition, [status(thm), theory('equality')], [c_48, c_770])).
% 2.60/1.46  tff(c_836, plain, (![A_1331, B_1332, D_1333]: (k2_xboole_0(k2_tarski(A_1331, B_1332), k1_tarski(D_1333))=k1_enumset1(A_1331, B_1332, D_1333))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_824])).
% 2.60/1.46  tff(c_896, plain, (![A_23, D_1333]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(D_1333))=k1_enumset1(A_23, A_23, D_1333))), inference(superposition, [status(thm), theory('equality')], [c_46, c_836])).
% 2.60/1.46  tff(c_932, plain, (![A_1424, D_1425]: (k2_xboole_0(k1_tarski(A_1424), k1_tarski(D_1425))=k2_tarski(A_1424, D_1425))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_896])).
% 2.60/1.46  tff(c_60, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.60/1.46  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.46  tff(c_139, plain, (![A_56, B_57]: (k2_xboole_0(A_56, k3_xboole_0(A_56, B_57))=A_56)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.46  tff(c_180, plain, (![B_63, A_64]: (k2_xboole_0(B_63, k3_xboole_0(A_64, B_63))=B_63)), inference(superposition, [status(thm), theory('equality')], [c_4, c_139])).
% 2.60/1.46  tff(c_193, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_60, c_180])).
% 2.60/1.46  tff(c_938, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_932, c_193])).
% 2.60/1.46  tff(c_211, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.46  tff(c_10, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.60/1.46  tff(c_217, plain, (![B_66, A_65]: (r2_hidden(B_66, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_211, c_10])).
% 2.60/1.46  tff(c_1053, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_938, c_217])).
% 2.60/1.46  tff(c_32, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.60/1.46  tff(c_1077, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1053, c_32])).
% 2.60/1.46  tff(c_1110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1077])).
% 2.60/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.46  
% 2.60/1.46  Inference rules
% 2.60/1.46  ----------------------
% 2.60/1.46  #Ref     : 0
% 2.60/1.46  #Sup     : 125
% 2.60/1.46  #Fact    : 0
% 2.60/1.46  #Define  : 0
% 2.60/1.46  #Split   : 1
% 2.60/1.46  #Chain   : 0
% 2.60/1.46  #Close   : 0
% 2.60/1.46  
% 2.60/1.46  Ordering : KBO
% 2.60/1.46  
% 2.60/1.46  Simplification rules
% 2.60/1.46  ----------------------
% 2.60/1.46  #Subsume      : 0
% 2.60/1.46  #Demod        : 31
% 2.60/1.46  #Tautology    : 63
% 2.60/1.46  #SimpNegUnit  : 1
% 2.60/1.46  #BackRed      : 0
% 2.60/1.46  
% 2.60/1.46  #Partial instantiations: 480
% 2.60/1.46  #Strategies tried      : 1
% 2.60/1.46  
% 2.60/1.46  Timing (in seconds)
% 2.60/1.46  ----------------------
% 2.60/1.46  Preprocessing        : 0.33
% 2.60/1.46  Parsing              : 0.17
% 2.60/1.46  CNF conversion       : 0.02
% 2.60/1.46  Main loop            : 0.33
% 2.60/1.46  Inferencing          : 0.16
% 2.60/1.46  Reduction            : 0.09
% 2.60/1.46  Demodulation         : 0.07
% 2.60/1.46  BG Simplification    : 0.02
% 2.60/1.46  Subsumption          : 0.05
% 2.60/1.46  Abstraction          : 0.02
% 2.60/1.46  MUC search           : 0.00
% 2.60/1.46  Cooper               : 0.00
% 2.60/1.46  Total                : 0.69
% 2.60/1.46  Index Insertion      : 0.00
% 2.60/1.46  Index Deletion       : 0.00
% 2.60/1.46  Index Matching       : 0.00
% 2.60/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
