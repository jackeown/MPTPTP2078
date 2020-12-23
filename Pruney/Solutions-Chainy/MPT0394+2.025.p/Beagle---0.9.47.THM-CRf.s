%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:24 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 105 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 ( 134 expanded)
%              Number of equality atoms :   42 (  96 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_103,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_82,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_171,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,B_76)
      | ~ r2_hidden(C_77,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_174,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_171])).

tff(c_56,plain,(
    ! [A_41] : k1_setfam_1(k1_tarski(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    ! [A_32,B_33,C_34] : k2_enumset1(A_32,A_32,B_33,C_34) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_380,plain,(
    ! [A_103,B_104,C_105,D_106] : k2_xboole_0(k1_enumset1(A_103,B_104,C_105),k1_tarski(D_106)) = k2_enumset1(A_103,B_104,C_105,D_106) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_389,plain,(
    ! [A_30,B_31,D_106] : k2_xboole_0(k2_tarski(A_30,B_31),k1_tarski(D_106)) = k2_enumset1(A_30,A_30,B_31,D_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_380])).

tff(c_393,plain,(
    ! [A_107,B_108,D_109] : k2_xboole_0(k2_tarski(A_107,B_108),k1_tarski(D_109)) = k1_enumset1(A_107,B_108,D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_389])).

tff(c_402,plain,(
    ! [A_29,D_109] : k2_xboole_0(k1_tarski(A_29),k1_tarski(D_109)) = k1_enumset1(A_29,A_29,D_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_393])).

tff(c_405,plain,(
    ! [A_29,D_109] : k2_xboole_0(k1_tarski(A_29),k1_tarski(D_109)) = k2_tarski(A_29,D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_402])).

tff(c_434,plain,(
    ! [A_113,B_114] :
      ( k3_xboole_0(k1_setfam_1(A_113),k1_setfam_1(B_114)) = k1_setfam_1(k2_xboole_0(A_113,B_114))
      | k1_xboole_0 = B_114
      | k1_xboole_0 = A_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4938,plain,(
    ! [A_7998,B_7999] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_7998),B_7999)) = k3_xboole_0(A_7998,k1_setfam_1(B_7999))
      | k1_xboole_0 = B_7999
      | k1_tarski(A_7998) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_434])).

tff(c_4980,plain,(
    ! [A_29,D_109] :
      ( k3_xboole_0(A_29,k1_setfam_1(k1_tarski(D_109))) = k1_setfam_1(k2_tarski(A_29,D_109))
      | k1_tarski(D_109) = k1_xboole_0
      | k1_tarski(A_29) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_4938])).

tff(c_5019,plain,(
    ! [A_8199,D_8200] :
      ( k1_setfam_1(k2_tarski(A_8199,D_8200)) = k3_xboole_0(A_8199,D_8200)
      | k1_tarski(D_8200) = k1_xboole_0
      | k1_tarski(A_8199) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4980])).

tff(c_58,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5045,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5019,c_58])).

tff(c_5048,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5045])).

tff(c_86,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_116,plain,(
    ! [B_58,A_59] : r2_hidden(B_58,k2_tarski(A_59,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_16])).

tff(c_119,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_116])).

tff(c_5162,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5048,c_119])).

tff(c_5190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_5162])).

tff(c_5191,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5045])).

tff(c_5306,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5191,c_119])).

tff(c_5334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_5306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.97  
% 5.01/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.97  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.01/1.97  
% 5.01/1.97  %Foreground sorts:
% 5.01/1.97  
% 5.01/1.97  
% 5.01/1.97  %Background operators:
% 5.01/1.97  
% 5.01/1.97  
% 5.01/1.97  %Foreground operators:
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.01/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.01/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/1.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.01/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.01/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.01/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.01/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.01/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.01/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.01/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.01/1.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.01/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.01/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.01/1.97  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.01/1.97  
% 5.36/1.98  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.36/1.98  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.36/1.98  tff(f_103, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 5.36/1.98  tff(f_82, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.36/1.98  tff(f_80, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.36/1.98  tff(f_84, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.36/1.98  tff(f_76, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 5.36/1.98  tff(f_101, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 5.36/1.98  tff(f_106, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.36/1.98  tff(f_72, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.36/1.98  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.36/1.98  tff(c_171, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, B_76) | ~r2_hidden(C_77, A_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.36/1.98  tff(c_174, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_171])).
% 5.36/1.98  tff(c_56, plain, (![A_41]: (k1_setfam_1(k1_tarski(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.36/1.98  tff(c_46, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.36/1.98  tff(c_44, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.36/1.98  tff(c_48, plain, (![A_32, B_33, C_34]: (k2_enumset1(A_32, A_32, B_33, C_34)=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.36/1.98  tff(c_380, plain, (![A_103, B_104, C_105, D_106]: (k2_xboole_0(k1_enumset1(A_103, B_104, C_105), k1_tarski(D_106))=k2_enumset1(A_103, B_104, C_105, D_106))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.36/1.98  tff(c_389, plain, (![A_30, B_31, D_106]: (k2_xboole_0(k2_tarski(A_30, B_31), k1_tarski(D_106))=k2_enumset1(A_30, A_30, B_31, D_106))), inference(superposition, [status(thm), theory('equality')], [c_46, c_380])).
% 5.36/1.98  tff(c_393, plain, (![A_107, B_108, D_109]: (k2_xboole_0(k2_tarski(A_107, B_108), k1_tarski(D_109))=k1_enumset1(A_107, B_108, D_109))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_389])).
% 5.36/1.98  tff(c_402, plain, (![A_29, D_109]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(D_109))=k1_enumset1(A_29, A_29, D_109))), inference(superposition, [status(thm), theory('equality')], [c_44, c_393])).
% 5.36/1.98  tff(c_405, plain, (![A_29, D_109]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(D_109))=k2_tarski(A_29, D_109))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_402])).
% 5.36/1.98  tff(c_434, plain, (![A_113, B_114]: (k3_xboole_0(k1_setfam_1(A_113), k1_setfam_1(B_114))=k1_setfam_1(k2_xboole_0(A_113, B_114)) | k1_xboole_0=B_114 | k1_xboole_0=A_113)), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.36/1.98  tff(c_4938, plain, (![A_7998, B_7999]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_7998), B_7999))=k3_xboole_0(A_7998, k1_setfam_1(B_7999)) | k1_xboole_0=B_7999 | k1_tarski(A_7998)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_434])).
% 5.36/1.98  tff(c_4980, plain, (![A_29, D_109]: (k3_xboole_0(A_29, k1_setfam_1(k1_tarski(D_109)))=k1_setfam_1(k2_tarski(A_29, D_109)) | k1_tarski(D_109)=k1_xboole_0 | k1_tarski(A_29)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_405, c_4938])).
% 5.36/1.98  tff(c_5019, plain, (![A_8199, D_8200]: (k1_setfam_1(k2_tarski(A_8199, D_8200))=k3_xboole_0(A_8199, D_8200) | k1_tarski(D_8200)=k1_xboole_0 | k1_tarski(A_8199)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4980])).
% 5.36/1.98  tff(c_58, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.36/1.98  tff(c_5045, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5019, c_58])).
% 5.36/1.98  tff(c_5048, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5045])).
% 5.36/1.98  tff(c_86, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.36/1.98  tff(c_16, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.36/1.98  tff(c_116, plain, (![B_58, A_59]: (r2_hidden(B_58, k2_tarski(A_59, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_16])).
% 5.36/1.98  tff(c_119, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_116])).
% 5.36/1.98  tff(c_5162, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5048, c_119])).
% 5.36/1.98  tff(c_5190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_5162])).
% 5.36/1.98  tff(c_5191, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5045])).
% 5.36/1.98  tff(c_5306, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5191, c_119])).
% 5.36/1.98  tff(c_5334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_5306])).
% 5.36/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/1.98  
% 5.36/1.98  Inference rules
% 5.36/1.98  ----------------------
% 5.36/1.98  #Ref     : 0
% 5.36/1.98  #Sup     : 773
% 5.36/1.98  #Fact    : 18
% 5.36/1.98  #Define  : 0
% 5.36/1.98  #Split   : 1
% 5.36/1.98  #Chain   : 0
% 5.36/1.98  #Close   : 0
% 5.36/1.98  
% 5.36/1.98  Ordering : KBO
% 5.36/1.98  
% 5.36/1.98  Simplification rules
% 5.36/1.98  ----------------------
% 5.36/1.98  #Subsume      : 147
% 5.36/1.98  #Demod        : 267
% 5.36/1.98  #Tautology    : 311
% 5.36/1.98  #SimpNegUnit  : 11
% 5.36/1.98  #BackRed      : 0
% 5.36/1.98  
% 5.36/1.98  #Partial instantiations: 3984
% 5.36/1.98  #Strategies tried      : 1
% 5.36/1.98  
% 5.36/1.98  Timing (in seconds)
% 5.36/1.98  ----------------------
% 5.36/1.99  Preprocessing        : 0.32
% 5.36/1.99  Parsing              : 0.17
% 5.36/1.99  CNF conversion       : 0.02
% 5.36/1.99  Main loop            : 0.90
% 5.36/1.99  Inferencing          : 0.46
% 5.36/1.99  Reduction            : 0.24
% 5.36/1.99  Demodulation         : 0.18
% 5.36/1.99  BG Simplification    : 0.04
% 5.36/1.99  Subsumption          : 0.12
% 5.36/1.99  Abstraction          : 0.05
% 5.36/1.99  MUC search           : 0.00
% 5.36/1.99  Cooper               : 0.00
% 5.36/1.99  Total                : 1.25
% 5.36/1.99  Index Insertion      : 0.00
% 5.36/1.99  Index Deletion       : 0.00
% 5.36/1.99  Index Matching       : 0.00
% 5.36/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
