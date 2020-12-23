%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:47 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (  64 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  58 expanded)
%              Number of equality atoms :   39 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] : k5_enumset1(A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [D_13,B_11,C_12,A_10] : k2_enumset1(D_13,B_11,C_12,A_10) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_227,plain,(
    ! [A_74,D_73,C_75,E_77,B_76] : k5_enumset1(A_74,A_74,A_74,B_76,C_75,D_73,E_77) = k3_enumset1(A_74,B_76,C_75,D_73,E_77) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [A_33,B_34,C_35] : k5_enumset1(A_33,A_33,A_33,A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_243,plain,(
    ! [C_78,D_79,E_80] : k3_enumset1(C_78,C_78,C_78,D_79,E_80) = k1_enumset1(C_78,D_79,E_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_38])).

tff(c_32,plain,(
    ! [A_21,B_22,C_23,D_24] : k3_enumset1(A_21,A_21,B_22,C_23,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_259,plain,(
    ! [C_81,D_82,E_83] : k2_enumset1(C_81,C_81,D_82,E_83) = k1_enumset1(C_81,D_82,E_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_32])).

tff(c_293,plain,(
    ! [A_84,B_85,C_86] : k2_enumset1(A_84,B_85,C_86,B_85) = k1_enumset1(B_85,C_86,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_259])).

tff(c_181,plain,(
    ! [A_66,B_67,C_68,D_69] : k2_xboole_0(k1_tarski(A_66),k1_enumset1(B_67,C_68,D_69)) = k2_enumset1(A_66,B_67,C_68,D_69) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [A_66,A_19,B_20] : k2_xboole_0(k1_tarski(A_66),k2_tarski(A_19,B_20)) = k2_enumset1(A_66,A_19,A_19,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_181])).

tff(c_304,plain,(
    ! [A_84,C_86] : k2_xboole_0(k1_tarski(A_84),k2_tarski(C_86,C_86)) = k1_enumset1(C_86,C_86,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_190])).

tff(c_340,plain,(
    ! [A_87,C_88] : k2_xboole_0(k1_tarski(A_87),k1_tarski(C_88)) = k2_tarski(C_88,A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_304])).

tff(c_2,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k4_xboole_0(B_46,A_45)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_84])).

tff(c_96,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_346,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_96])).

tff(c_10,plain,(
    ! [D_9,B_5] : r2_hidden(D_9,k2_tarski(D_9,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_368,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_10])).

tff(c_101,plain,(
    ! [D_47,B_48,A_49] :
      ( D_47 = B_48
      | D_47 = A_49
      | ~ r2_hidden(D_47,k2_tarski(A_49,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [D_47,A_18] :
      ( D_47 = A_18
      | D_47 = A_18
      | ~ r2_hidden(D_47,k1_tarski(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_101])).

tff(c_376,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_368,c_104])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.23  
% 2.03/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.23  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.03/1.23  
% 2.03/1.23  %Foreground sorts:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Background operators:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Foreground operators:
% 2.03/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.23  
% 2.12/1.24  tff(f_59, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.12/1.24  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.12/1.24  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.24  tff(f_40, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 2.12/1.24  tff(f_50, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 2.12/1.24  tff(f_54, axiom, (![A, B, C]: (k5_enumset1(A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_enumset1)).
% 2.12/1.24  tff(f_48, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.12/1.24  tff(f_42, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.12/1.24  tff(f_27, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.12/1.24  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.12/1.24  tff(f_38, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.12/1.24  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.24  tff(c_30, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.24  tff(c_28, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.24  tff(c_24, plain, (![D_13, B_11, C_12, A_10]: (k2_enumset1(D_13, B_11, C_12, A_10)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.24  tff(c_227, plain, (![A_74, D_73, C_75, E_77, B_76]: (k5_enumset1(A_74, A_74, A_74, B_76, C_75, D_73, E_77)=k3_enumset1(A_74, B_76, C_75, D_73, E_77))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.24  tff(c_38, plain, (![A_33, B_34, C_35]: (k5_enumset1(A_33, A_33, A_33, A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.12/1.24  tff(c_243, plain, (![C_78, D_79, E_80]: (k3_enumset1(C_78, C_78, C_78, D_79, E_80)=k1_enumset1(C_78, D_79, E_80))), inference(superposition, [status(thm), theory('equality')], [c_227, c_38])).
% 2.12/1.24  tff(c_32, plain, (![A_21, B_22, C_23, D_24]: (k3_enumset1(A_21, A_21, B_22, C_23, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.24  tff(c_259, plain, (![C_81, D_82, E_83]: (k2_enumset1(C_81, C_81, D_82, E_83)=k1_enumset1(C_81, D_82, E_83))), inference(superposition, [status(thm), theory('equality')], [c_243, c_32])).
% 2.12/1.24  tff(c_293, plain, (![A_84, B_85, C_86]: (k2_enumset1(A_84, B_85, C_86, B_85)=k1_enumset1(B_85, C_86, A_84))), inference(superposition, [status(thm), theory('equality')], [c_24, c_259])).
% 2.12/1.24  tff(c_181, plain, (![A_66, B_67, C_68, D_69]: (k2_xboole_0(k1_tarski(A_66), k1_enumset1(B_67, C_68, D_69))=k2_enumset1(A_66, B_67, C_68, D_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.12/1.24  tff(c_190, plain, (![A_66, A_19, B_20]: (k2_xboole_0(k1_tarski(A_66), k2_tarski(A_19, B_20))=k2_enumset1(A_66, A_19, A_19, B_20))), inference(superposition, [status(thm), theory('equality')], [c_30, c_181])).
% 2.12/1.24  tff(c_304, plain, (![A_84, C_86]: (k2_xboole_0(k1_tarski(A_84), k2_tarski(C_86, C_86))=k1_enumset1(C_86, C_86, A_84))), inference(superposition, [status(thm), theory('equality')], [c_293, c_190])).
% 2.12/1.24  tff(c_340, plain, (![A_87, C_88]: (k2_xboole_0(k1_tarski(A_87), k1_tarski(C_88))=k2_tarski(C_88, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_304])).
% 2.12/1.24  tff(c_2, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.24  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.24  tff(c_84, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k4_xboole_0(B_46, A_45))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.24  tff(c_93, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_84])).
% 2.12/1.24  tff(c_96, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_93])).
% 2.12/1.24  tff(c_346, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_340, c_96])).
% 2.12/1.24  tff(c_10, plain, (![D_9, B_5]: (r2_hidden(D_9, k2_tarski(D_9, B_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.24  tff(c_368, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_10])).
% 2.12/1.24  tff(c_101, plain, (![D_47, B_48, A_49]: (D_47=B_48 | D_47=A_49 | ~r2_hidden(D_47, k2_tarski(A_49, B_48)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.24  tff(c_104, plain, (![D_47, A_18]: (D_47=A_18 | D_47=A_18 | ~r2_hidden(D_47, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_101])).
% 2.12/1.24  tff(c_376, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_368, c_104])).
% 2.12/1.24  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_376])).
% 2.12/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  Inference rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Ref     : 0
% 2.12/1.24  #Sup     : 82
% 2.12/1.24  #Fact    : 0
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 0
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 0
% 2.12/1.24  #Demod        : 15
% 2.12/1.24  #Tautology    : 56
% 2.12/1.24  #SimpNegUnit  : 1
% 2.12/1.24  #BackRed      : 0
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.29
% 2.12/1.24  Parsing              : 0.15
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.19
% 2.12/1.25  Inferencing          : 0.07
% 2.12/1.25  Reduction            : 0.07
% 2.12/1.25  Demodulation         : 0.05
% 2.12/1.25  BG Simplification    : 0.01
% 2.12/1.25  Subsumption          : 0.03
% 2.12/1.25  Abstraction          : 0.01
% 2.12/1.25  MUC search           : 0.00
% 2.12/1.25  Cooper               : 0.00
% 2.12/1.25  Total                : 0.51
% 2.12/1.25  Index Insertion      : 0.00
% 2.12/1.25  Index Deletion       : 0.00
% 2.12/1.25  Index Matching       : 0.00
% 2.12/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
