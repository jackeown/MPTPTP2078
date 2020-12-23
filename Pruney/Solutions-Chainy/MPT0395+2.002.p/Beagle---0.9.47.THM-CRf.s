%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:28 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   55 (  61 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 (  73 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_3'(A_21,B_22),A_21)
      | r1_setfam_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_226,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(k4_xboole_0(A_61,B_62),C_63)
      | ~ r1_tarski(A_61,k2_xboole_0(B_62,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_135,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_146,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_230,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,k2_xboole_0(B_62,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_226,c_146])).

tff(c_250,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k1_xboole_0
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_230])).

tff(c_266,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_250])).

tff(c_36,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_359,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_36])).

tff(c_369,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32,c_359])).

tff(c_176,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_511,plain,(
    ! [D_81,A_82,B_83] :
      ( r2_hidden(D_81,A_82)
      | ~ r2_hidden(D_81,k3_xboole_0(A_82,B_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_8])).

tff(c_535,plain,(
    ! [D_84] :
      ( r2_hidden(D_84,'#skF_6')
      | ~ r2_hidden(D_84,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_511])).

tff(c_904,plain,(
    ! [B_114] :
      ( r2_hidden('#skF_3'('#skF_5',B_114),'#skF_6')
      | r1_setfam_1('#skF_5',B_114) ) ),
    inference(resolution,[status(thm)],[c_46,c_535])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_347,plain,(
    ! [A_68,B_69,D_70] :
      ( ~ r1_tarski('#skF_3'(A_68,B_69),D_70)
      | ~ r2_hidden(D_70,B_69)
      | r1_setfam_1(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_352,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden('#skF_3'(A_68,B_69),B_69)
      | r1_setfam_1(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_26,c_347])).

tff(c_908,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_904,c_352])).

tff(c_912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_908])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.36  
% 2.73/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.37  %$ r2_hidden > r1_tarski > r1_setfam_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.73/1.37  
% 2.73/1.37  %Foreground sorts:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Background operators:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Foreground operators:
% 2.73/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.37  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.73/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.73/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.73/1.37  
% 2.73/1.38  tff(f_76, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.73/1.38  tff(f_69, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.73/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.73/1.38  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.73/1.38  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.73/1.38  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.73/1.38  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.38  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.38  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.73/1.38  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.73/1.38  tff(c_50, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.73/1.38  tff(c_46, plain, (![A_21, B_22]: (r2_hidden('#skF_3'(A_21, B_22), A_21) | r1_setfam_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.73/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.38  tff(c_32, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.38  tff(c_52, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.73/1.38  tff(c_28, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.73/1.38  tff(c_226, plain, (![A_61, B_62, C_63]: (r1_tarski(k4_xboole_0(A_61, B_62), C_63) | ~r1_tarski(A_61, k2_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.38  tff(c_30, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.38  tff(c_135, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.38  tff(c_146, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_135])).
% 2.73/1.38  tff(c_230, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, k2_xboole_0(B_62, k1_xboole_0)))), inference(resolution, [status(thm)], [c_226, c_146])).
% 2.73/1.38  tff(c_250, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k1_xboole_0 | ~r1_tarski(A_64, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_230])).
% 2.73/1.38  tff(c_266, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_250])).
% 2.73/1.38  tff(c_36, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.73/1.38  tff(c_359, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_266, c_36])).
% 2.73/1.38  tff(c_369, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32, c_359])).
% 2.73/1.38  tff(c_176, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.73/1.38  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.38  tff(c_511, plain, (![D_81, A_82, B_83]: (r2_hidden(D_81, A_82) | ~r2_hidden(D_81, k3_xboole_0(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_8])).
% 2.73/1.38  tff(c_535, plain, (![D_84]: (r2_hidden(D_84, '#skF_6') | ~r2_hidden(D_84, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_511])).
% 2.73/1.38  tff(c_904, plain, (![B_114]: (r2_hidden('#skF_3'('#skF_5', B_114), '#skF_6') | r1_setfam_1('#skF_5', B_114))), inference(resolution, [status(thm)], [c_46, c_535])).
% 2.73/1.38  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.38  tff(c_347, plain, (![A_68, B_69, D_70]: (~r1_tarski('#skF_3'(A_68, B_69), D_70) | ~r2_hidden(D_70, B_69) | r1_setfam_1(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.73/1.38  tff(c_352, plain, (![A_68, B_69]: (~r2_hidden('#skF_3'(A_68, B_69), B_69) | r1_setfam_1(A_68, B_69))), inference(resolution, [status(thm)], [c_26, c_347])).
% 2.73/1.38  tff(c_908, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_904, c_352])).
% 2.73/1.38  tff(c_912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_908])).
% 2.73/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  Inference rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Ref     : 0
% 2.73/1.38  #Sup     : 201
% 2.73/1.38  #Fact    : 0
% 2.73/1.38  #Define  : 0
% 2.73/1.38  #Split   : 1
% 2.73/1.38  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.38  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 23
% 2.73/1.38  #Demod        : 66
% 2.73/1.38  #Tautology    : 118
% 2.73/1.38  #SimpNegUnit  : 1
% 2.73/1.38  #BackRed      : 1
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.73/1.38  Preprocessing        : 0.31
% 2.73/1.38  Parsing              : 0.16
% 2.73/1.38  CNF conversion       : 0.02
% 2.73/1.38  Main loop            : 0.31
% 2.73/1.38  Inferencing          : 0.11
% 2.73/1.38  Reduction            : 0.10
% 2.73/1.38  Demodulation         : 0.07
% 2.73/1.38  BG Simplification    : 0.02
% 2.73/1.38  Subsumption          : 0.06
% 2.73/1.38  Abstraction          : 0.02
% 2.73/1.38  MUC search           : 0.00
% 2.73/1.38  Cooper               : 0.00
% 2.73/1.38  Total                : 0.65
% 2.73/1.38  Index Insertion      : 0.00
% 2.73/1.38  Index Deletion       : 0.00
% 2.73/1.38  Index Matching       : 0.00
% 2.73/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
