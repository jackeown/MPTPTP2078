%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:53 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  71 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_271,plain,(
    ! [A_74,B_75,C_76,D_77] : k2_xboole_0(k1_enumset1(A_74,B_75,C_76),k1_tarski(D_77)) = k2_enumset1(A_74,B_75,C_76,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_280,plain,(
    ! [A_19,B_20,D_77] : k2_xboole_0(k2_tarski(A_19,B_20),k1_tarski(D_77)) = k2_enumset1(A_19,A_19,B_20,D_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_271])).

tff(c_284,plain,(
    ! [A_78,B_79,D_80] : k2_xboole_0(k2_tarski(A_78,B_79),k1_tarski(D_80)) = k1_enumset1(A_78,B_79,D_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_280])).

tff(c_293,plain,(
    ! [A_18,D_80] : k2_xboole_0(k1_tarski(A_18),k1_tarski(D_80)) = k1_enumset1(A_18,A_18,D_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_284])).

tff(c_297,plain,(
    ! [A_81,D_82] : k2_xboole_0(k1_tarski(A_81),k1_tarski(D_82)) = k2_tarski(A_81,D_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_293])).

tff(c_46,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_164,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_168,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_164])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_45,B_46] : k2_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_172,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_101])).

tff(c_306,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_172])).

tff(c_134,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_140,plain,(
    ! [B_50,A_49] : r2_hidden(B_50,k2_tarski(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_10])).

tff(c_332,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_140])).

tff(c_232,plain,(
    ! [E_65,C_66,B_67,A_68] :
      ( E_65 = C_66
      | E_65 = B_67
      | E_65 = A_68
      | ~ r2_hidden(E_65,k1_enumset1(A_68,B_67,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_251,plain,(
    ! [E_69,B_70,A_71] :
      ( E_69 = B_70
      | E_69 = A_71
      | E_69 = A_71
      | ~ r2_hidden(E_69,k2_tarski(A_71,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_232])).

tff(c_260,plain,(
    ! [E_69,A_18] :
      ( E_69 = A_18
      | E_69 = A_18
      | E_69 = A_18
      | ~ r2_hidden(E_69,k1_tarski(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_251])).

tff(c_340,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_332,c_260])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_44,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.66  
% 2.48/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.67  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.48/1.67  
% 2.48/1.67  %Foreground sorts:
% 2.48/1.67  
% 2.48/1.67  
% 2.48/1.67  %Background operators:
% 2.48/1.67  
% 2.48/1.67  
% 2.48/1.67  %Foreground operators:
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.48/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.67  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.67  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.48/1.67  
% 2.63/1.68  tff(f_65, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.63/1.68  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.63/1.68  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.63/1.68  tff(f_56, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.63/1.68  tff(f_50, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.63/1.68  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.63/1.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.63/1.68  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.63/1.68  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.63/1.68  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.68  tff(c_36, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.63/1.68  tff(c_34, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.68  tff(c_38, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.63/1.68  tff(c_271, plain, (![A_74, B_75, C_76, D_77]: (k2_xboole_0(k1_enumset1(A_74, B_75, C_76), k1_tarski(D_77))=k2_enumset1(A_74, B_75, C_76, D_77))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.68  tff(c_280, plain, (![A_19, B_20, D_77]: (k2_xboole_0(k2_tarski(A_19, B_20), k1_tarski(D_77))=k2_enumset1(A_19, A_19, B_20, D_77))), inference(superposition, [status(thm), theory('equality')], [c_36, c_271])).
% 2.63/1.68  tff(c_284, plain, (![A_78, B_79, D_80]: (k2_xboole_0(k2_tarski(A_78, B_79), k1_tarski(D_80))=k1_enumset1(A_78, B_79, D_80))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_280])).
% 2.63/1.68  tff(c_293, plain, (![A_18, D_80]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(D_80))=k1_enumset1(A_18, A_18, D_80))), inference(superposition, [status(thm), theory('equality')], [c_34, c_284])).
% 2.63/1.68  tff(c_297, plain, (![A_81, D_82]: (k2_xboole_0(k1_tarski(A_81), k1_tarski(D_82))=k2_tarski(A_81, D_82))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_293])).
% 2.63/1.68  tff(c_46, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.68  tff(c_164, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.68  tff(c_168, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_46, c_164])).
% 2.63/1.68  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.63/1.68  tff(c_92, plain, (![A_45, B_46]: (k2_xboole_0(A_45, k3_xboole_0(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.68  tff(c_101, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_92])).
% 2.63/1.68  tff(c_172, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_168, c_101])).
% 2.63/1.68  tff(c_306, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_297, c_172])).
% 2.63/1.68  tff(c_134, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.63/1.68  tff(c_10, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.63/1.68  tff(c_140, plain, (![B_50, A_49]: (r2_hidden(B_50, k2_tarski(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_10])).
% 2.63/1.68  tff(c_332, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_140])).
% 2.63/1.68  tff(c_232, plain, (![E_65, C_66, B_67, A_68]: (E_65=C_66 | E_65=B_67 | E_65=A_68 | ~r2_hidden(E_65, k1_enumset1(A_68, B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.63/1.68  tff(c_251, plain, (![E_69, B_70, A_71]: (E_69=B_70 | E_69=A_71 | E_69=A_71 | ~r2_hidden(E_69, k2_tarski(A_71, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_232])).
% 2.63/1.68  tff(c_260, plain, (![E_69, A_18]: (E_69=A_18 | E_69=A_18 | E_69=A_18 | ~r2_hidden(E_69, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_251])).
% 2.63/1.68  tff(c_340, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_332, c_260])).
% 2.63/1.68  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_44, c_340])).
% 2.63/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.68  
% 2.63/1.68  Inference rules
% 2.63/1.68  ----------------------
% 2.63/1.68  #Ref     : 0
% 2.63/1.68  #Sup     : 75
% 2.63/1.68  #Fact    : 0
% 2.63/1.68  #Define  : 0
% 2.63/1.68  #Split   : 0
% 2.63/1.68  #Chain   : 0
% 2.63/1.68  #Close   : 0
% 2.63/1.68  
% 2.63/1.68  Ordering : KBO
% 2.63/1.69  
% 2.63/1.69  Simplification rules
% 2.63/1.69  ----------------------
% 2.63/1.69  #Subsume      : 0
% 2.63/1.69  #Demod        : 16
% 2.63/1.69  #Tautology    : 57
% 2.63/1.69  #SimpNegUnit  : 1
% 2.63/1.69  #BackRed      : 0
% 2.63/1.69  
% 2.63/1.69  #Partial instantiations: 0
% 2.63/1.69  #Strategies tried      : 1
% 2.63/1.69  
% 2.63/1.69  Timing (in seconds)
% 2.63/1.69  ----------------------
% 2.63/1.69  Preprocessing        : 0.46
% 2.63/1.69  Parsing              : 0.22
% 2.63/1.69  CNF conversion       : 0.04
% 2.63/1.69  Main loop            : 0.31
% 2.63/1.69  Inferencing          : 0.11
% 2.63/1.69  Reduction            : 0.11
% 2.63/1.69  Demodulation         : 0.08
% 2.63/1.69  BG Simplification    : 0.02
% 2.63/1.69  Subsumption          : 0.05
% 2.63/1.69  Abstraction          : 0.02
% 2.63/1.69  MUC search           : 0.00
% 2.63/1.69  Cooper               : 0.00
% 2.63/1.69  Total                : 0.82
% 2.63/1.69  Index Insertion      : 0.00
% 2.63/1.69  Index Deletion       : 0.00
% 2.63/1.69  Index Matching       : 0.00
% 2.63/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
