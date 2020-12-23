%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:00 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_912,plain,(
    ! [A_1272,B_1273,C_1274,D_1275] : k2_xboole_0(k2_tarski(A_1272,B_1273),k2_tarski(C_1274,D_1275)) = k2_enumset1(A_1272,B_1273,C_1274,D_1275) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    ! [B_22,A_21,C_23] : k2_xboole_0(k2_tarski(B_22,A_21),k2_tarski(C_23,A_21)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_938,plain,(
    ! [A_1311,D_1312,C_1313] : k2_enumset1(A_1311,D_1312,C_1313,D_1312) = k1_enumset1(D_1312,A_1311,C_1313) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_44])).

tff(c_54,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_953,plain,(
    ! [D_1312,C_1313] : k1_enumset1(D_1312,D_1312,C_1313) = k1_enumset1(D_1312,C_1313,D_1312) ),
    inference(superposition,[status(thm),theory(equality)],[c_938,c_54])).

tff(c_973,plain,(
    ! [D_1312,C_1313] : k1_enumset1(D_1312,C_1313,D_1312) = k2_tarski(D_1312,C_1313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_953])).

tff(c_50,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_700,plain,(
    ! [A_1087,B_1088,C_1089,D_1090] : k2_xboole_0(k1_tarski(A_1087),k1_enumset1(B_1088,C_1089,D_1090)) = k2_enumset1(A_1087,B_1088,C_1089,D_1090) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_748,plain,(
    ! [A_1087,A_34,B_35] : k2_xboole_0(k1_tarski(A_1087),k2_tarski(A_34,B_35)) = k2_enumset1(A_1087,A_34,A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_700])).

tff(c_964,plain,(
    ! [A_1087,B_35] : k2_xboole_0(k1_tarski(A_1087),k2_tarski(B_35,B_35)) = k1_enumset1(B_35,A_1087,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_938])).

tff(c_976,plain,(
    ! [A_1087,B_35] : k2_xboole_0(k1_tarski(A_1087),k1_tarski(B_35)) = k1_enumset1(B_35,A_1087,B_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_964])).

tff(c_1031,plain,(
    ! [A_1421,B_1422] : k2_xboole_0(k1_tarski(A_1421),k1_tarski(B_1422)) = k2_tarski(B_1422,A_1421) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_976])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1041,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_60])).

tff(c_84,plain,(
    ! [A_56,B_57] : k1_enumset1(A_56,A_56,B_57) = k2_tarski(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [E_11,B_6,C_7] : r2_hidden(E_11,k1_enumset1(E_11,B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [A_56,B_57] : r2_hidden(A_56,k2_tarski(A_56,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_12])).

tff(c_1154,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_96])).

tff(c_30,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1183,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1154,c_30])).

tff(c_1216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.44  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.73/1.44  
% 2.73/1.44  %Foreground sorts:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Background operators:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Foreground operators:
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.73/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.73/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.73/1.44  
% 2.73/1.45  tff(f_72, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.73/1.45  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.73/1.45  tff(f_53, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.73/1.45  tff(f_55, axiom, (![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 2.73/1.45  tff(f_65, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.73/1.45  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.73/1.45  tff(f_57, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.73/1.45  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.73/1.45  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.73/1.45  tff(c_58, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.73/1.45  tff(c_52, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.73/1.45  tff(c_912, plain, (![A_1272, B_1273, C_1274, D_1275]: (k2_xboole_0(k2_tarski(A_1272, B_1273), k2_tarski(C_1274, D_1275))=k2_enumset1(A_1272, B_1273, C_1274, D_1275))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.45  tff(c_44, plain, (![B_22, A_21, C_23]: (k2_xboole_0(k2_tarski(B_22, A_21), k2_tarski(C_23, A_21))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.73/1.45  tff(c_938, plain, (![A_1311, D_1312, C_1313]: (k2_enumset1(A_1311, D_1312, C_1313, D_1312)=k1_enumset1(D_1312, A_1311, C_1313))), inference(superposition, [status(thm), theory('equality')], [c_912, c_44])).
% 2.73/1.45  tff(c_54, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.73/1.45  tff(c_953, plain, (![D_1312, C_1313]: (k1_enumset1(D_1312, D_1312, C_1313)=k1_enumset1(D_1312, C_1313, D_1312))), inference(superposition, [status(thm), theory('equality')], [c_938, c_54])).
% 2.73/1.45  tff(c_973, plain, (![D_1312, C_1313]: (k1_enumset1(D_1312, C_1313, D_1312)=k2_tarski(D_1312, C_1313))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_953])).
% 2.73/1.45  tff(c_50, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.45  tff(c_700, plain, (![A_1087, B_1088, C_1089, D_1090]: (k2_xboole_0(k1_tarski(A_1087), k1_enumset1(B_1088, C_1089, D_1090))=k2_enumset1(A_1087, B_1088, C_1089, D_1090))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.73/1.45  tff(c_748, plain, (![A_1087, A_34, B_35]: (k2_xboole_0(k1_tarski(A_1087), k2_tarski(A_34, B_35))=k2_enumset1(A_1087, A_34, A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_52, c_700])).
% 2.73/1.45  tff(c_964, plain, (![A_1087, B_35]: (k2_xboole_0(k1_tarski(A_1087), k2_tarski(B_35, B_35))=k1_enumset1(B_35, A_1087, B_35))), inference(superposition, [status(thm), theory('equality')], [c_748, c_938])).
% 2.73/1.45  tff(c_976, plain, (![A_1087, B_35]: (k2_xboole_0(k1_tarski(A_1087), k1_tarski(B_35))=k1_enumset1(B_35, A_1087, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_964])).
% 2.73/1.45  tff(c_1031, plain, (![A_1421, B_1422]: (k2_xboole_0(k1_tarski(A_1421), k1_tarski(B_1422))=k2_tarski(B_1422, A_1421))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_976])).
% 2.73/1.45  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.73/1.45  tff(c_1041, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1031, c_60])).
% 2.73/1.45  tff(c_84, plain, (![A_56, B_57]: (k1_enumset1(A_56, A_56, B_57)=k2_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.73/1.45  tff(c_12, plain, (![E_11, B_6, C_7]: (r2_hidden(E_11, k1_enumset1(E_11, B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.45  tff(c_96, plain, (![A_56, B_57]: (r2_hidden(A_56, k2_tarski(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_12])).
% 2.73/1.45  tff(c_1154, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_96])).
% 2.73/1.45  tff(c_30, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.73/1.45  tff(c_1183, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1154, c_30])).
% 2.73/1.45  tff(c_1216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1183])).
% 2.73/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  Inference rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Ref     : 0
% 2.73/1.45  #Sup     : 146
% 2.73/1.45  #Fact    : 0
% 2.73/1.45  #Define  : 0
% 2.73/1.45  #Split   : 2
% 2.73/1.45  #Chain   : 0
% 2.73/1.45  #Close   : 0
% 2.73/1.45  
% 2.73/1.45  Ordering : KBO
% 2.73/1.45  
% 2.73/1.45  Simplification rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Subsume      : 3
% 2.73/1.45  #Demod        : 50
% 2.73/1.45  #Tautology    : 77
% 2.73/1.45  #SimpNegUnit  : 1
% 2.73/1.45  #BackRed      : 1
% 2.73/1.45  
% 2.73/1.45  #Partial instantiations: 585
% 2.73/1.45  #Strategies tried      : 1
% 2.73/1.45  
% 2.73/1.45  Timing (in seconds)
% 2.73/1.45  ----------------------
% 2.98/1.45  Preprocessing        : 0.31
% 2.98/1.45  Parsing              : 0.15
% 2.98/1.45  CNF conversion       : 0.02
% 2.98/1.45  Main loop            : 0.35
% 2.98/1.45  Inferencing          : 0.18
% 2.98/1.45  Reduction            : 0.09
% 2.98/1.45  Demodulation         : 0.06
% 2.98/1.45  BG Simplification    : 0.02
% 2.98/1.45  Subsumption          : 0.05
% 2.98/1.45  Abstraction          : 0.02
% 2.98/1.45  MUC search           : 0.00
% 2.98/1.45  Cooper               : 0.00
% 2.98/1.45  Total                : 0.68
% 2.98/1.45  Index Insertion      : 0.00
% 2.98/1.45  Index Deletion       : 0.00
% 2.98/1.45  Index Matching       : 0.00
% 2.98/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
