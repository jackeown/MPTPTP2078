%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:44 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 144 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   48 ( 163 expanded)
%              Number of equality atoms :   42 ( 150 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    ! [A_56,B_57,C_58,D_59] : k2_xboole_0(k1_enumset1(A_56,B_57,C_58),k1_tarski(D_59)) = k2_enumset1(A_56,B_57,C_58,D_59) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    ! [A_18,B_19,D_59] : k2_xboole_0(k2_tarski(A_18,B_19),k1_tarski(D_59)) = k2_enumset1(A_18,A_18,B_19,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_143])).

tff(c_156,plain,(
    ! [A_60,B_61,D_62] : k2_xboole_0(k2_tarski(A_60,B_61),k1_tarski(D_62)) = k1_enumset1(A_60,B_61,D_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_152])).

tff(c_165,plain,(
    ! [A_17,D_62] : k2_xboole_0(k1_tarski(A_17),k1_tarski(D_62)) = k1_enumset1(A_17,A_17,D_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_156])).

tff(c_168,plain,(
    ! [A_17,D_62] : k2_xboole_0(k1_tarski(A_17),k1_tarski(D_62)) = k2_tarski(A_17,D_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_188,plain,(
    ! [A_67,D_68] : k2_xboole_0(k1_tarski(A_67),k1_tarski(D_68)) = k2_tarski(A_67,D_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k4_xboole_0(B_43,A_42)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_92])).

tff(c_104,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_101])).

tff(c_194,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_104])).

tff(c_155,plain,(
    ! [A_18,B_19,D_59] : k2_xboole_0(k2_tarski(A_18,B_19),k1_tarski(D_59)) = k1_enumset1(A_18,B_19,D_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_152])).

tff(c_206,plain,(
    ! [D_59] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_59)) = k1_enumset1('#skF_4','#skF_3',D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_155])).

tff(c_219,plain,(
    ! [D_69] : k1_enumset1('#skF_4','#skF_3',D_69) = k2_tarski('#skF_4',D_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_206])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_234,plain,(
    ! [D_69] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_12])).

tff(c_169,plain,(
    ! [E_63,C_64,B_65,A_66] :
      ( E_63 = C_64
      | E_63 = B_65
      | E_63 = A_66
      | ~ r2_hidden(E_63,k1_enumset1(A_66,B_65,C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_265,plain,(
    ! [E_77,B_78,A_79] :
      ( E_77 = B_78
      | E_77 = A_79
      | E_77 = A_79
      | ~ r2_hidden(E_77,k2_tarski(A_79,B_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_169])).

tff(c_268,plain,(
    ! [D_69] :
      ( D_69 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_234,c_265])).

tff(c_289,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_268])).

tff(c_283,plain,(
    ! [D_69] : D_69 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_268])).

tff(c_400,plain,(
    ! [D_1022] : D_1022 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_283])).

tff(c_503,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.32  
% 2.41/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.32  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.41/1.32  
% 2.41/1.32  %Foreground sorts:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Background operators:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Foreground operators:
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.41/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.41/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.41/1.32  
% 2.41/1.33  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.41/1.33  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.41/1.33  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.41/1.33  tff(f_54, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.41/1.33  tff(f_48, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.41/1.33  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.41/1.33  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.41/1.33  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.41/1.33  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.41/1.33  tff(c_36, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.41/1.33  tff(c_34, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.33  tff(c_38, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.33  tff(c_143, plain, (![A_56, B_57, C_58, D_59]: (k2_xboole_0(k1_enumset1(A_56, B_57, C_58), k1_tarski(D_59))=k2_enumset1(A_56, B_57, C_58, D_59))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.41/1.33  tff(c_152, plain, (![A_18, B_19, D_59]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_tarski(D_59))=k2_enumset1(A_18, A_18, B_19, D_59))), inference(superposition, [status(thm), theory('equality')], [c_36, c_143])).
% 2.41/1.33  tff(c_156, plain, (![A_60, B_61, D_62]: (k2_xboole_0(k2_tarski(A_60, B_61), k1_tarski(D_62))=k1_enumset1(A_60, B_61, D_62))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_152])).
% 2.41/1.33  tff(c_165, plain, (![A_17, D_62]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(D_62))=k1_enumset1(A_17, A_17, D_62))), inference(superposition, [status(thm), theory('equality')], [c_34, c_156])).
% 2.41/1.33  tff(c_168, plain, (![A_17, D_62]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(D_62))=k2_tarski(A_17, D_62))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_165])).
% 2.41/1.33  tff(c_188, plain, (![A_67, D_68]: (k2_xboole_0(k1_tarski(A_67), k1_tarski(D_68))=k2_tarski(A_67, D_68))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_165])).
% 2.41/1.33  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.33  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.41/1.33  tff(c_92, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k4_xboole_0(B_43, A_42))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.33  tff(c_101, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_92])).
% 2.41/1.33  tff(c_104, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_101])).
% 2.41/1.33  tff(c_194, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_188, c_104])).
% 2.41/1.33  tff(c_155, plain, (![A_18, B_19, D_59]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_tarski(D_59))=k1_enumset1(A_18, B_19, D_59))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_152])).
% 2.41/1.33  tff(c_206, plain, (![D_59]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_59))=k1_enumset1('#skF_4', '#skF_3', D_59))), inference(superposition, [status(thm), theory('equality')], [c_194, c_155])).
% 2.41/1.33  tff(c_219, plain, (![D_69]: (k1_enumset1('#skF_4', '#skF_3', D_69)=k2_tarski('#skF_4', D_69))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_206])).
% 2.41/1.33  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.33  tff(c_234, plain, (![D_69]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_69)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_12])).
% 2.41/1.33  tff(c_169, plain, (![E_63, C_64, B_65, A_66]: (E_63=C_64 | E_63=B_65 | E_63=A_66 | ~r2_hidden(E_63, k1_enumset1(A_66, B_65, C_64)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.33  tff(c_265, plain, (![E_77, B_78, A_79]: (E_77=B_78 | E_77=A_79 | E_77=A_79 | ~r2_hidden(E_77, k2_tarski(A_79, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_169])).
% 2.41/1.33  tff(c_268, plain, (![D_69]: (D_69='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_234, c_265])).
% 2.41/1.33  tff(c_289, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_268])).
% 2.41/1.33  tff(c_283, plain, (![D_69]: (D_69='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_268])).
% 2.41/1.33  tff(c_400, plain, (![D_1022]: (D_1022='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_289, c_283])).
% 2.41/1.33  tff(c_503, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_400, c_42])).
% 2.41/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  Inference rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Ref     : 0
% 2.41/1.33  #Sup     : 156
% 2.41/1.33  #Fact    : 0
% 2.41/1.33  #Define  : 0
% 2.41/1.33  #Split   : 0
% 2.41/1.33  #Chain   : 0
% 2.41/1.33  #Close   : 0
% 2.41/1.33  
% 2.41/1.33  Ordering : KBO
% 2.41/1.33  
% 2.41/1.33  Simplification rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Subsume      : 31
% 2.41/1.33  #Demod        : 23
% 2.41/1.33  #Tautology    : 53
% 2.41/1.33  #SimpNegUnit  : 1
% 2.41/1.33  #BackRed      : 0
% 2.41/1.33  
% 2.41/1.33  #Partial instantiations: 30
% 2.41/1.33  #Strategies tried      : 1
% 2.41/1.33  
% 2.41/1.33  Timing (in seconds)
% 2.41/1.33  ----------------------
% 2.41/1.33  Preprocessing        : 0.31
% 2.41/1.33  Parsing              : 0.16
% 2.41/1.33  CNF conversion       : 0.02
% 2.41/1.33  Main loop            : 0.27
% 2.41/1.33  Inferencing          : 0.12
% 2.41/1.33  Reduction            : 0.08
% 2.41/1.33  Demodulation         : 0.06
% 2.41/1.33  BG Simplification    : 0.02
% 2.41/1.33  Subsumption          : 0.04
% 2.41/1.33  Abstraction          : 0.01
% 2.41/1.33  MUC search           : 0.00
% 2.41/1.33  Cooper               : 0.00
% 2.41/1.33  Total                : 0.60
% 2.41/1.33  Index Insertion      : 0.00
% 2.41/1.33  Index Deletion       : 0.00
% 2.41/1.33  Index Matching       : 0.00
% 2.41/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
